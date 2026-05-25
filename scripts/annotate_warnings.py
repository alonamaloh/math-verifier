#!/usr/bin/env python3
"""Inject warning comments inline into source files.

Reads `make library` output on stdin, finds lines of the form
  `warning: Module.name:LINE:COL: ...message...`
maps Module.name back to its library/.../path.math source file,
and inserts a comment of the form
  `-- WARNING(LINE:COL): ...message...`
right above the cited line.

Idempotent: existing `-- WARNING(...)` lines are stripped first so a
re-run reflects the current warning set, not an accumulation.

Usage:
  rm -f build/library/*/*.mathv
  make -j 16 library 2>&1 | python3 scripts/annotate_warnings.py
"""
import os
import re
import sys
from collections import defaultdict

WARNING_RE = re.compile(
    r"^warning:\s+([\w.]+):(\d+):(\d+):\s+(.*)$")

LIBRARY_ROOT = "library"

def module_to_path(module_name: str) -> str:
    parts = module_name.split(".")
    return os.path.join(LIBRARY_ROOT, *parts[:-1], parts[-1] + ".math")

def strip_existing_annotations(path: str) -> list[str]:
    with open(path) as f:
        lines = f.readlines()
    return [ln for ln in lines if not re.match(r"^\s*-- WARNING\(", ln)]

def main() -> int:
    warnings_by_module: dict[str, list[tuple[int, int, str]]] = defaultdict(list)
    for raw in sys.stdin:
        match = WARNING_RE.match(raw.rstrip("\n"))
        if not match:
            continue
        module, line, col, message = match.groups()
        warnings_by_module[module].append((int(line), int(col), message))

    if not warnings_by_module:
        print("no warnings parsed from stdin", file=sys.stderr)
        return 0

    total = 0
    for module, warnings in sorted(warnings_by_module.items()):
        path = module_to_path(module)
        if not os.path.isfile(path):
            print(f"skip: {module}: source not found at {path}",
                  file=sys.stderr)
            continue
        lines = strip_existing_annotations(path)
        # Re-collect warnings against the stripped file: their LINE
        # numbers came from the version we just compiled (which has no
        # annotation lines, since we wiped build/ before make), so they
        # already match the stripped indexing. Sort descending so
        # insertions don't shift later line numbers.
        for line_num, col, message in sorted(warnings,
                                              key=lambda w: -w[0]):
            if line_num < 1 or line_num > len(lines):
                continue
            indent = re.match(r"^(\s*)", lines[line_num - 1]).group(1)
            annotation = f"{indent}-- WARNING({line_num}:{col}): {message}\n"
            lines.insert(line_num - 1, annotation)
            total += 1
        with open(path, "w") as f:
            f.writelines(lines)
        print(f"annotated {path}: {len(warnings)} warning(s)",
              file=sys.stderr)

    print(f"total annotations injected: {total}", file=sys.stderr)
    return 0

if __name__ == "__main__":
    sys.exit(main())
