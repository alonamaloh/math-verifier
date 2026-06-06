#!/usr/bin/env python3
"""Mark redundant-`by` and redundant-calc-step locations as inline comments.

Runs the kernel's `--check-redundant-by` and `--check-redundant-calc-steps`
diagnostics on each given .math file and appends a marker comment to every
flagged source line. The marker carries the EXACT warning text the kernel
emitted (wrapped in `«…»`), so the fix instructions travel with the marker —
no need to recall what a terse tag like `UNUSED-NAME` was shorthand for. (That
shorthand is what led to whole claims being deleted when only the *name* was
redundant.) Markers are inserted in descending line order so earlier insertions
never shift the line numbers of later ones.

Then a human (or a lesser LLM) applies the flagged fix BY HAND, rebuilds, and
reverts anything that turns out to be a false positive (the checker tests each
site in isolation, so adjacent steps in a chain can interact).

Usage:  python3 .mark_redundant.py library/Foo/bar.math [more.math ...]
        python3 .mark_redundant.py --unmark library/Foo/bar.math   # strip markers
"""
import os
import re
import subprocess
import sys

# A marker is the verbatim warning message wrapped in guillemets. `«` appears
# nowhere else in the library, so unmark can strip any `-- «…»` tail — this also
# catches the older terse-tag markers (`«UNUSED-NAME»`, `«REDUNDANT-BY»`, …).
WARNING_RE = re.compile(r"^warning: [^:]+:(\d+)(?::\d+)?: (.*)$")
MARK_RE = re.compile(r"\s*-- «[^»]*»\s*$")


def run_check(path):
    """Run all three redundancy diagnostics in one pass (cost-limited)."""
    out = f"/tmp/mark_{os.getpid()}.mathv"  # unique per process for -P safety
    result = subprocess.run(
        ["./kernel", "verify", "--source", path, "--output", out,
         "--cache-root", "build",
         "--check-redundant-by", "--check-redundant-by-non-eq",
         "--check-redundant-calc-steps"],
        capture_output=True, text=True)
    try:
        os.remove(out)
    except OSError:
        pass
    return result.stdout + result.stderr


def collect(path):
    """Return {line_number: marker} — marker is the verbatim warning text.

    Only the first warning per line is kept: a marker lives at the end of its
    source line, so a line can carry exactly one. Identical duplicate warnings
    (the checker sometimes emits a pair) collapse harmlessly.
    """
    marks = {}
    for line in run_check(path).splitlines():
        m = WARNING_RE.match(line)
        if not m:
            continue
        ln = int(m.group(1))
        message = m.group(2).strip()
        marks.setdefault(ln, "  -- «" + message + "»")
    return marks


def unmark(path):
    with open(path) as f:
        lines = f.readlines()
    out = [MARK_RE.sub("", ln.rstrip("\n")) + "\n" for ln in lines]
    with open(path, "w") as f:
        f.writelines(out)


def mark(path):
    marks = collect(path)
    if not marks:
        print(f"{path}: clean")
        return
    with open(path) as f:
        lines = f.readlines()
    for line_number in sorted(marks, reverse=True):  # later first
        index = line_number - 1
        if 0 <= index < len(lines):
            stripped = lines[index].rstrip("\n")
            if not MARK_RE.search(stripped):
                lines[index] = stripped + marks[line_number] + "\n"
    with open(path, "w") as f:
        f.writelines(lines)
    print(f"{path}: marked {len(marks)} site(s) at lines "
          f"{sorted(marks, reverse=True)}")


if __name__ == "__main__":
    args = sys.argv[1:]
    if args and args[0] == "--unmark":
        for p in args[1:]:
            unmark(p)
    else:
        for p in args:
            mark(p)
