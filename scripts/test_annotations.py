"""Regression tests for author markers versus unmarked Lean documentation."""
import unittest
from copy import deepcopy
from check_annotations import annotation_inventory, uncomment, validate_annotation_module


class AnnotationInventoryTests(unittest.TestCase):
    def test_legacy_and_doc_markers(self):
        result = annotation_inventory(
            '/- AUTHOR-PROSE-01\nFirst.\n-/\n'
            '/- AUTHOR-SPAN RP-01\nSecond.\n-/\n'
            '/-- AUTHOR-SPAN CF-01\nThird. -/')
        self.assertEqual(result['annotation_ids'], ['AUTHOR-PROSE-01', 'RP-01', 'CF-01'])
        self.assertEqual(result['unmarked_comments'], dict(block=0, doc=0, module=0))

    def test_nested_comments_and_fake_markers(self):
        source = ('/- Prose /- nested -/ continues. -/\n'
                  '/-- Documentation. -/\n/-! Heading. -/\n'
                  '-- /- AUTHOR-SPAN RP-99\n'
                  'def text := "/- AUTHOR-SPAN RP-99\\nFake -/"\n')
        result = annotation_inventory(source)
        self.assertEqual(result['annotation_ids'], [])
        self.assertEqual(result['unmarked_comments'], dict(block=1, doc=1, module=1))
        comments = []
        self.assertEqual(uncomment(source), uncomment(source, comments))
        self.assertEqual(len(comments), 3)

    def test_invalid_markers(self):
        cases = [
            '/- AUTHOR-SPAN RP-01\nOne. -/ /- AUTHOR-SPAN RP-01\nTwo. -/',
            '/- AUTHOR-SPAN RP-01 -/',
            '/- AUTHOR-SPAN RP-01\n /- empty -/ -/',
            '/- AUTHOR-SPAN RP-x\nText. -/',
            '/-! AUTHOR-SPAN RP-01\nText. -/',
            '/- unterminated',
        ]
        for source in cases:
            with self.subTest(source=source), self.assertRaises(AssertionError):
                annotation_inventory(source)

    def test_unicode_body_location_and_module_target(self):
        source = 'MutualEvaluation/Public/Example.lean'
        text = '-- α😀\n/-- AUTHOR-SPAN CF-02\n  A β /- nested -/ sentence.  -/\ndef x := 1\n'
        result = annotation_inventory(text, source)
        record = result['annotations'][0]
        selector = record['body']['selector']
        self.assertEqual(text[selector['start']:selector['end']],
                         'A β /- nested -/ sentence.')
        self.assertEqual(selector['start'], text.index('A β'))
        self.assertEqual(record['body']['source'], source)
        self.assertEqual(record['target'], {'id': source, 'format': 'text/plain'})
        self.assertEqual(record['creator']['name'], 'Zachary Robertson')
        self.assertEqual(record['id'], 'CF-02')
        self.assertEqual(result['annotation_ids'], ['CF-02'])

    def test_stale_selectors_and_metadata_are_rejected(self):
        text = '/- AUTHOR-SPAN RP-01\nA passage. -/'
        expected = annotation_inventory(text, 'Example.lean')
        validate_annotation_module(text, 'Example.lean', expected)
        for field, value in [('id', 'RP-99'), ('creator', {}),
                             ('body', {}), ('target', {'id': 'wrong.lean'})]:
            stale = deepcopy(expected)
            stale['annotations'][0][field] = value
            with self.subTest(field=field), self.assertRaises(AssertionError):
                validate_annotation_module(text, 'Example.lean', stale)
        for changed in ('-- inserted line\n' + text, text + text, ''):
            with self.subTest(changed=changed), self.assertRaises(AssertionError):
                validate_annotation_module(changed, 'Example.lean', expected)
        stale = deepcopy(expected)
        stale['annotation_ids'] = []
        with self.assertRaises(AssertionError):
            validate_annotation_module(text, 'Example.lean', stale)

    def test_unknown_module_docs_and_line_comments_stay_unattributed(self):
        text = ('-- AUTHOR-SPAN CO-99\n'
                '/- AUTHOR-SPAN AB-08\nConfirmed prose. -/\n'
                '/-! All-law statements: an unknown creator. -/\n'
                '/-! Reachable-law statements: an unknown creator. -/\n'
                '/-- AUTHOR-SPAN AB-11\nConfirmed doc comment. -/')
        result = annotation_inventory(text)
        self.assertEqual(result['annotation_ids'], ['AB-08', 'AB-11'])
        self.assertEqual(result['unmarked_comments'], dict(block=0, doc=0, module=2))
        self.assertEqual([a['id'] for a in result['annotations']], ['AB-08', 'AB-11'])


if __name__ == '__main__':
    unittest.main()
