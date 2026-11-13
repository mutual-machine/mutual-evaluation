"""Regression tests for author markers versus unmarked Lean documentation."""
import unittest
from check_annotations import annotation_inventory, uncomment


class AnnotationInventoryTests(unittest.TestCase):
    def test_legacy_and_doc_markers(self):
        result = annotation_inventory(
            '/- AUTHOR-PROSE-01\nFirst.\n-/\n'
            '/- AUTHOR-SPAN RP-01\nSecond.\n-/\n'
            '/-- AUTHOR-SPAN CF-01\nThird. -/')
        self.assertEqual(result['author_ids'], ['AUTHOR-PROSE-01', 'RP-01', 'CF-01'])
        self.assertEqual(result['unmarked_comments'], dict(block=0, doc=0, module=0))

    def test_nested_comments_and_fake_markers(self):
        source = ('/- Prose /- nested -/ continues. -/\n'
                  '/-- Documentation. -/\n/-! Heading. -/\n'
                  '-- /- AUTHOR-SPAN RP-99\n'
                  'def text := "/- AUTHOR-SPAN RP-99\\nFake -/"\n')
        result = annotation_inventory(source)
        self.assertEqual(result['author_ids'], [])
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


if __name__ == '__main__':
    unittest.main()
