#!/usr/bin/env python3
"""Verify that library documentation still tells the truth.

Scans every .md file under library/ for backticked qualified names
(`Natural.gcd_is_gcd`, `Matrix.IsEscalation`, ...) and checks that each
one still resolves to a declaration in the library sources. A name that
no longer resolves means the documentation has drifted (a rename, a
removal, or a fabrication) — exactly the failure mode that makes a
README worse than no README, since agents trust it over grepping.

Also enforces the documentation vocabulary rules: the retired terms
`claim` and `calc` must not appear as proof vocabulary, and `successor`
may appear only in Natural/'s own docs (the boundary that owns the
prohibition may spell it out; everywhere else the word itself is
avoided so examples never display it).

Usage:
  scripts/check_library_docs.py            # check, exit 1 on findings
  scripts/check_library_docs.py --list     # dump every checked name
"""

import os
import re
import sys
import glob

LIBRARY = "library"

# Declaration heads that introduce citable names in .math sources.
DECLARATION = re.compile(
    r"^(?:automatic\s+)?"
    r"(?:theorem|definition|opaque\s+definition|axiom|inductive|construction|instance)\s+"
    r"([A-Za-z_][A-Za-z0-9_.]*)",
    re.MULTILINE,
)
# Inductive constructors: `  | name` (qualified or bare — a bare name
# inherits the enclosing inductive's namespace).
INDUCTIVE_HEAD = re.compile(r"^inductive\s+([A-Za-z_][A-Za-z0-9_.]*)", re.MULTILINE)
CONSTRUCTOR = re.compile(r"^\s*\|\s*([A-Za-z_][A-Za-z0-9_.]*)", re.MULTILINE)

# A backticked qualified name in the docs: starts with a capitalized
# component, has at least one dot, optionally applied / suffixed.
DOC_NAME = re.compile(r"`([A-Z][A-Za-z0-9_]*(?:\.[A-Za-z0-9_]+)+)[^`]*`")

# Mentions that are legitimately not declarations (families described
# with a wildcard, file paths, purely-notational names). Suffix `*`
# matches any extension of the prefix.
SKIP = []
SKIP_PREFIXES = [
    "Tutorial.",           # tutorial-only example names
]


def declared_names():
    names = set()
    for path in glob.glob(os.path.join(LIBRARY, "**", "*.math"), recursive=True):
        text = open(path, encoding="utf-8").read()
        for m in DECLARATION.finditer(text):
            names.add(m.group(1).rstrip("."))
        # Constructors: only meaningful inside an inductive block; a bare
        # constructor name is qualified by the enclosing inductive.
        for head in INDUCTIVE_HEAD.finditer(text):
            inductive = head.group(1).rstrip(".")
            where = text.find("where", head.end())
            if where < 0:
                continue
            block = text[where + len("where"):]
            for line in block.splitlines()[1:]:
                m = re.match(r"\s*\|\s*([A-Za-z_][A-Za-z0-9_.]*)", line)
                if m:
                    name = m.group(1)
                    names.add(name if "." in name else f"{inductive}.{name}")
                elif line.strip() and not line.lstrip().startswith("--"):
                    break
        # Module names double as citable paths (`Natural.order` the module).
        rel = os.path.relpath(path, LIBRARY)
        names.add(rel[:-len(".math")].replace(os.sep, "."))
    return names


def doc_mentions():
    for path in sorted(glob.glob(os.path.join(LIBRARY, "**", "*.md"), recursive=True)):
        text = open(path, encoding="utf-8").read()
        for m in DOC_NAME.finditer(text):
            name = m.group(1).rstrip(".")
            line = text.count("\n", 0, m.start()) + 1
            yield path, line, name


def main():
    list_mode = "--list" in sys.argv
    declared = declared_names()
    failures = []
    checked = 0

    for path, line, name in doc_mentions():
        if any(name == s for s in SKIP):
            continue
        if name.endswith(".md") or name.endswith(".math"):
            continue
        if any(name.startswith(p) for p in SKIP_PREFIXES):
            continue
        # A dotted name may be cited at an outer or inner qualification
        # (`Natural.to_integer.add_preserves` declares the full path;
        # `IsEnumerable.quotient` declares exactly itself). Accept a
        # mention when the name or any dotted extension of it is
        # declared (covers `Foo.bar` cited while `Foo.bar.baz`-style
        # accessor families are the declarations).
        checked += 1
        if name in declared or any(d.startswith(name + ".") for d in declared):
            if list_mode:
                print(f"ok    {name}    ({path}:{line})")
            continue
        failures.append((path, line, name))

    # Vocabulary rules (docs_vocabulary_rules): retired terms must not
    # appear anywhere; `successor` only inside Natural/'s own docs (the
    # boundary that owns the prohibition may spell it out).
    retired = re.compile(r"`(claim|calc)`")
    successor = re.compile(r"\bsuccessor\b")
    for path in sorted(glob.glob(os.path.join(LIBRARY, "**", "*.md"), recursive=True)):
        in_natural = os.sep + "Natural" + os.sep in path
        for i, line_text in enumerate(open(path, encoding="utf-8"), 1):
            m = retired.search(line_text)
            if m:
                failures.append((path, i, f"forbidden vocabulary: {m.group(0)!r}"))
            if not in_natural and successor.search(line_text):
                failures.append((path, i, "forbidden vocabulary: 'successor' outside Natural/"))

    if failures:
        print(f"library-docs check: {len(failures)} finding(s) over {checked} checked names:")
        for path, line, what in failures:
            print(f"  {path}:{line}: {what}")
        return 1
    print(f"library-docs check: OK ({checked} names resolve, vocabulary clean)")
    return 0


if __name__ == "__main__":
    sys.exit(main())
