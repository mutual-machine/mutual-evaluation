#!/usr/bin/env python3
"""Check Public source ownership and audit coverage, without external baselines.

Public Lean files own the declarations and annotations. These checks detect
structural inconsistencies, not changes in mathematical meaning or author intent.
Lean checks types and proofs; interface changes still require author review.
"""
from pathlib import Path
import re
import json

ROOT = Path(__file__).resolve().parents[1]
PUBLIC = ROOT / "MutualEvaluation/Public"

# Counts and audit routing are technical regression checks, not annotations.
MODULES = {
    "Core": (8, "Core"),
    "TwoPairOutcome": (14, "TwoPairOutcome"),
    "Abstract": (13, "Abstract"),
    "CriticTiming": (24, "PublicTiming"),
    "Replication": (70, "PublicReplication"),
    "Certification": (5, "PublicCertification"),
}


def uncomment(text, comments=None, spans=None):
    """Remove nested comments; optionally collect outer block comments verbatim."""
    output = []
    i = 0
    while i < len(text):
        if text.startswith("/-", i):
            start = i
            depth = 1
            i += 2
            while depth:
                assert i < len(text), "Unterminated block comment"
                if text.startswith("/-", i):
                    depth += 1
                    i += 2
                elif text.startswith("-/", i):
                    depth -= 1
                    i += 2
                else:
                    i += 1
            if comments is not None:
                comments.append(text[start:i])
            if spans is not None:
                spans.append((start, i))
            output.append("".join("\n" if c == "\n" else " " for c in text[start:i]))
        elif text.startswith("--", i):
            end = text.find("\n", i)
            if end < 0:
                end = len(text)
            output.append(" " * (end - i))
            i = end
        elif text[i] == '"':
            end = i + 1
            while end < len(text):
                if text[end] == "\\":
                    end += 2
                elif text[end] == '"':
                    end += 1
                    break
                else:
                    end += 1
            output.append(text[i:end])
            i = end
        else:
            output.append(text[i])
            i += 1
    return "".join(output)


DECL = re.compile(
    r"(?m)^(?:(?:private|protected) )?(def|abbrev|theorem|structure)\s+"
    r"([^\s(:]+)[^\n]*(?:\n[ \t]+[^\n]*)*"
)
SCOPE = re.compile(
    r"(?m)^(namespace\s+\S+|(?:noncomputable\s+)?section(?:\s+\S+)?|end(?:\s+\S+)?)\s*$"
)


def normalize(text):
    return re.sub(r"\s+", " ", text).strip()


def declarations(text, qualified=False):
    """Extract this project's top-level indented declaration syntax."""
    text = uncomment(text)
    scopes = list(SCOPE.finditer(text))
    result = []
    for match in DECL.finditer(text):
        kind, name = match[1], match[2]
        value = match[0]
        if kind == "theorem":
            value = value.split(":=", 1)[0]
        if qualified:
            stack = []
            for scope in scopes:
                if scope.start() >= match.start():
                    break
                command = scope[1].strip()
                if command.startswith("namespace "):
                    stack.append(command.split()[1])
                elif command.startswith("end"):
                    assert stack, "Unbalanced scope"
                    stack.pop()
                else:
                    stack.append(None)
            name = ".".join([s for s in stack if s] + [name])
        result.append((kind, name, normalize(value)))
    return result


def public_declarations():
    """Read declaration inventories from their authoritative Public source sites."""
    assert {p.stem for p in PUBLIC.glob("*.lean")} == set(MODULES), \
        "Public module inventory changed; update coverage after author review"
    return {
        module: declarations((PUBLIC / (module + ".lean")).read_text(), qualified=True)
        for module in MODULES
    }


def project_import_closure(module):
    """Follow project imports independently of successful Lean elaboration."""
    seen = set()
    pending = [module]
    while pending:
        current = pending.pop()
        if current in seen:
            continue
        seen.add(current)
        path = ROOT / (current.replace(".", "/") + ".lean")
        assert path.is_file(), ("Missing project import", current)
        pending.extend(
            name for name in re.findall(r"^import (\S+)$", uncomment(path.read_text()), re.M)
            if name.startswith("MutualEvaluation"))
    return seen


# Retain legacy timing IDs and the module-prefixed AUTHOR-SPAN convention.
AUTHOR = re.compile(r"(AUTHOR-PROSE-\d+|AUTHOR-SPAN [A-Z]+-\d+)\n(.*)", re.S)


CREATOR = {"id": "https://github.com/zrobertson466920",
           "type": "Person", "name": "Zachary Robertson"}


def annotation_inventory(text, source="Example.lean"):
    """Count explicit author markers separately from other documentation.

    A doc comment can carry an author marker without losing its Lean doc status.
    Unmarked comments are not evidence of authorship; line comments are excluded.
    """
    comments = []
    spans = []
    uncomment(text, comments, spans)
    ids = []
    annotations = []
    unmarked = dict(block=0, doc=0, module=0)
    for comment, (offset, _) in zip(comments, spans):
        kind = "doc" if comment.startswith("/--") else (
            "module" if comment.startswith("/-!") else "block")
        opener = 3 if kind != "block" else 2
        inner = comment[opener:-2]
        body = inner.strip()
        marker = AUTHOR.fullmatch(body)
        if marker:
            assert kind != "module", "Author marker in module heading"
            name = marker[1].removeprefix("AUTHOR-SPAN ")
            assert uncomment(marker[2]).strip(), (name, "empty annotation")
            assert name not in ids, (name, "duplicate annotation ID")
            ids.append(name)
            prose = marker[2]
            start = (offset + opener + len(inner) - len(inner.lstrip())
                     + marker.start(2) + len(prose) - len(prose.lstrip()))
            annotations.append({
                "id": name,
                "type": "Annotation",
                "creator": dict(CREATOR),
                "body": {
                    "type": "SpecificResource",
                    "source": source,
                    "selector": {"type": "TextPositionSelector", "start": start,
                                 "end": start + len(prose.strip())},
                },
                # Conservatively target the containing module, not a guessed declaration.
                "target": {"id": source, "format": "text/plain"},
            })
        else:
            assert "AUTHOR-" not in body, "Malformed author annotation marker"
            unmarked[kind] += 1
    return {"annotation_ids": ids, "unmarked_comments": unmarked,
            "annotations": annotations}


def validate_annotation_module(text, source, expected):
    """Check current structure/coverage, not authorship history or prose preservation."""
    actual = annotation_inventory(text, source)
    assert actual == expected, (source, "annotation inventory changed", actual)
    return actual


def check_annotation_inventory():
    expected = json.loads((ROOT / "scripts/annotation_inventory.json").read_text())
    assert set(expected) == set(MODULES), "Annotation module inventory changed"
    counts = {}
    seen = set()
    for module in MODULES:
        source = f"MutualEvaluation/Public/{module}.lean"
        actual = validate_annotation_module((ROOT / source).read_text(encoding="utf-8"),
                                            source, expected[module])
        ids = actual["annotation_ids"]
        assert not seen.intersection(ids), (module, "annotation ID reused across modules")
        seen.update(ids)
        counts[module] = len(ids)
        other = actual["unmarked_comments"]
        print(f"PASS {module}: {len(ids)} author passages; unmarked comments "
              f"{other['block']} block, {other['doc']} doc, {other['module']} module.")
    return counts


def check():
    assert project_import_closure("MutualEvaluation.Public.Core") == {
        "MutualEvaluation.Public.Core"
    }, "Core must not import paper declarations"
    assert project_import_closure("MutualEvaluation.Internal.ReplicationExpressions") == {
        "MutualEvaluation.Internal.ReplicationExpressions",
        "MutualEvaluation.Public.Core",
    }, "ReplicationExpressions must use only shared project prerequisites"
    selected = public_declarations()
    owners = {}
    for path in (ROOT / "MutualEvaluation").rglob("*.lean"):
        for _, name, _ in declarations(path.read_text(), qualified=True):
            owners.setdefault(name, []).append(str(path.relative_to(ROOT)))

    for module, items in selected.items():
        count, batch = MODULES[module]
        assert len(items) == count, (module, "declaration count changed", len(items))
        text = (PUBLIC / (module + ".lean")).read_text()
        assert "```lean" not in text, (module, "use real Lean declarations")
        assert not re.search(r"\b(sorry|admit|sorryAx|axiom)\b", uncomment(text)), \
            (module, "unexpected placeholder or axiom declaration")
        names = [name for _, name, _ in items]
        assert len(names) == len(set(names)), (module, "duplicate declaration")
        for name in names:
            assert owners.get(name) == [
                f"MutualEvaluation/Public/{module}.lean"
            ], (name, owners.get(name))
        audit = (ROOT / "Audit" / (batch + ".lean")).read_text()
        inspected = re.findall(r"^#print axioms (\S+)$", audit, re.M)
        if module in {"Core", "TwoPairOutcome"}:
            # These inspections open MutualEvaluation and use short names.
            inspected = ["MutualEvaluation." + name for name in inspected]
            displayed = re.findall(r"^#print (?!axioms\b)(\S+)$", audit, re.M)
            assert ["MutualEvaluation." + name for name in displayed] == names
        elif module == "Abstract":
            # This batch opens MutualEvaluation.Abstract and groups by topic.
            inspected = ["MutualEvaluation.Abstract." + name for name in inspected]
        # Order is immaterial to coverage; sorting still detects duplicate reports.
        assert sorted(inspected) == sorted(names), (
            module, "audit coverage differs from Public source",
            {"missing": sorted(set(names) - set(inspected)),
             "extra": sorted(set(inspected) - set(names))})
        print(f"PASS {module}: {count} declarations, unique ownership, exact audit coverage.")

    timing = selected["CriticTiming"]
    replication = selected["Replication"]
    assert sum(k == "theorem" for k, _, _ in timing) == 9
    assert sum(k == "theorem" for k, _, _ in replication) == 34
    annotation_counts = check_annotation_inventory()
    root_imports = re.findall(
        r"^import (\S+)$", (ROOT / "MutualEvaluation.lean").read_text(), re.M)
    assert root_imports == ["MutualEvaluation.Public." + module for module in MODULES]
    print(f"PASS {sum(count for count, _ in MODULES.values())} Public declarations; "
          f"{sum(annotation_counts.values())} marked author annotation passages.")
    print("Public Lean sources are authoritative; these checks do not certify author intent.")


if __name__ == "__main__":
    check()
