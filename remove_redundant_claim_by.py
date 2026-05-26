#!/usr/bin/env python3
"""
Strip `by <proof>` annotations from claim sites that the redundant-by
check has flagged.

For each warning of the form
    warning: <Module.Path>:<line>: redundant `by` on `claim` — ...
locate the `claim ... by <proof>;` at that source line, then rewrite it
as `claim ... ;` (deleting the `by <proof>` portion). The `;` stays.

Edits are made bottom-up per file so earlier line numbers don't shift.
After all edits, rebuild and report.
"""

import re
import subprocess
import sys
from pathlib import Path

REPO_ROOT = Path("/Users/alvaro/claude/math")


def collect_warnings():
    """Force full rebuild, return sorted list of (file, lineno) for
    each `redundant by on claim` warning."""
    subprocess.run(
        ["sh", "-c", "find build -name '*.mathv' -delete 2>/dev/null"],
        cwd=REPO_ROOT,
    )
    result = subprocess.run(
        ["make", "-j", "16", "library"],
        cwd=REPO_ROOT, capture_output=True, text=True,
    )
    if result.returncode != 0:
        sys.stderr.write("baseline build failed:\n")
        sys.stderr.write(result.stderr or result.stdout)
        sys.exit(1)
    pattern = re.compile(
        r"warning:\s+([\w.]+):(\d+)(?::\d+)?:\s+redundant `by` on `claim`"
    )
    seen = set()
    out = []
    for line in result.stdout.splitlines() + result.stderr.splitlines():
        m = pattern.search(line)
        if not m:
            continue
        module = m.group(1)
        lineno = int(m.group(2))
        file_path = REPO_ROOT / "library" / (module.replace(".", "/") + ".math")
        key = (file_path, lineno)
        if key in seen:
            continue
        seen.add(key)
        out.append(key)
    return out


def is_word_boundary(text, pos):
    if pos < 0 or pos >= len(text):
        return True
    c = text[pos]
    return not (c.isalnum() or c == "_")


def find_line_start(text, lineno):
    """Offset of the first character on `lineno` (1-indexed)."""
    pos = 0
    current = 1
    while current < lineno and pos < len(text):
        if text[pos] == "\n":
            current += 1
        pos += 1
    return pos


def skip_comment_or_advance(text, pos):
    """If we're at `-- ...` comment start, skip past EOL. Returns new pos."""
    if pos + 1 < len(text) and text[pos] == "-" and text[pos + 1] == "-":
        eol = text.find("\n", pos)
        return len(text) if eol < 0 else eol + 1
    return pos + 1


def remove_by_at(file_path: Path, lineno: int) -> bool:
    """Locate the claim at `lineno` and strip its `by <proof>` portion.

    Walks forward from the start of `lineno` tracking paren/bracket depth.
    Finds the `by` keyword at depth 0 (relative to the claim's surrounding
    block), then finds the matching `;` at the same depth.
    """
    text = file_path.read_text()
    start = find_line_start(text, lineno)
    # Skip leading whitespace on the claim's line; the `claim` keyword
    # should be there. We don't strictly verify since the script trusts
    # the warning's location.
    pos = start
    depth = 0
    by_pos = None
    while pos < len(text):
        # Inline comment.
        if (
            depth == 0
            and pos + 1 < len(text)
            and text[pos] == "-"
            and text[pos + 1] == "-"
        ):
            pos = skip_comment_or_advance(text, pos)
            continue
        c = text[pos]
        if c in "({[":
            depth += 1
        elif c in ")}]":
            depth -= 1
            if depth < 0:
                sys.stderr.write(
                    f"  ! depth went negative scanning {file_path}:{lineno}\n"
                )
                return False
        elif (
            depth == 0
            and c == "b"
            and text[pos:pos + 2] == "by"
            and is_word_boundary(text, pos - 1)
            and is_word_boundary(text, pos + 2)
        ):
            by_pos = pos
            break
        pos += 1
    if by_pos is None:
        sys.stderr.write(f"  ! couldn't find `by` at {file_path}:{lineno}\n")
        return False
    # Now find the `;` at depth 0 after by_pos.
    pos = by_pos + 2
    depth = 0
    semi_pos = None
    while pos < len(text):
        if (
            depth == 0
            and pos + 1 < len(text)
            and text[pos] == "-"
            and text[pos + 1] == "-"
        ):
            pos = skip_comment_or_advance(text, pos)
            continue
        c = text[pos]
        if c in "({[":
            depth += 1
        elif c in ")}]":
            depth -= 1
        elif depth == 0 and c == ";":
            semi_pos = pos
            break
        pos += 1
    if semi_pos is None:
        sys.stderr.write(
            f"  ! couldn't find `;` after `by` at {file_path}:{lineno}\n"
        )
        return False
    # Trim trailing whitespace before by_pos (including newlines) so
    # the `;` attaches to the preceding content line instead of
    # stranding on its own. We leave at most one newline at the end
    # of the next line so the file's final newline is preserved.
    trim_start = by_pos
    while trim_start > 0 and text[trim_start - 1] in " \t\n":
        trim_start -= 1
    new_text = text[:trim_start] + text[semi_pos:]
    file_path.write_text(new_text)
    return True


def main():
    warnings = collect_warnings()
    print(f"{len(warnings)} `redundant by on claim` warning(s) to clean")
    if not warnings:
        return 0
    # Group by file. Within a file, sort descending by line so we edit
    # from the bottom up.
    by_file = {}
    for fp, ln in warnings:
        by_file.setdefault(fp, []).append(ln)
    for fp in by_file:
        by_file[fp].sort(reverse=True)
    failed = []
    for fp, lines in by_file.items():
        for ln in lines:
            print(f"  {fp.relative_to(REPO_ROOT)}:{ln}")
            if not remove_by_at(fp, ln):
                failed.append((fp, ln))
    if failed:
        sys.stderr.write(f"\n{len(failed)} location(s) failed to edit\n")
    print("\nrebuilding to verify...")
    rebuild = subprocess.run(
        ["sh", "-c", "find build -name '*.mathv' -delete 2>/dev/null"],
        cwd=REPO_ROOT,
    )
    result = subprocess.run(
        ["make", "-j", "16", "library"],
        cwd=REPO_ROOT, capture_output=True, text=True,
    )
    print("(rebuild output suppressed; status: %s)" % (
        "ok" if result.returncode == 0 else "FAILED"
    ))
    if result.returncode != 0:
        sys.stderr.write(result.stderr or result.stdout)
        sys.exit(1)
    # Report residual redundant-by warnings.
    new_warnings = []
    pattern = re.compile(r"warning:.*redundant `by` on")
    for line in result.stdout.splitlines() + result.stderr.splitlines():
        if pattern.search(line):
            new_warnings.append(line)
    print(f"residual redundant-by warnings: {len(new_warnings)}")
    for w in new_warnings:
        print(f"  {w}")
    return 0 if not failed else 1


if __name__ == "__main__":
    sys.exit(main())
