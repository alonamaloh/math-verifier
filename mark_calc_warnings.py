#!/usr/bin/env python3
"""
Force a fresh full library build, parse the verifier's warnings, and
insert a single-line `-- WARN: <kind> ...` comment IMMEDIATELY ABOVE
each flagged source line. After running this, walk through each file
by hand: read the marker, Edit the site, delete the marker.

Bottom-up insertion per file so earlier line numbers don't shift
under us. Markers carry the warning's column and a one-line gloss of
what the warning is asking for.

Re-runs are safe: existing `-- WARN:` markers are stripped before
the new pass inserts fresh ones.
"""

import re
import subprocess
import sys
from pathlib import Path

REPO_ROOT = Path("/Users/alvaro/claude/math")
MARKER_PREFIX = "-- WARN:"

# Files where extra checks (`--check-redundant-by-non-eq`,
# `--check-redundant-calc-steps`) take too long to be useful in a
# default cleanup pass. Skip the per-file verify by faking up an
# unchanged `.mathv` from the existing cache before the build, so make
# treats them as up-to-date. Standalone targets: pass --skip to also
# skip them.
SLOW_FILES = [
    "library/Real/supremum.math",
    "library/PAdic/absolute_value.math",
]


def force_full_build(extra_flags=None, skip_slow=False):
    subprocess.run(
        ["sh", "-c", "find build -name '*.mathv' -delete 2>/dev/null"],
        cwd=REPO_ROOT,
    )
    if skip_slow:
        # First do a regular build so the slow files' .mathv exist.
        # Then delete every OTHER .mathv to force re-verify of the rest
        # with the extra flags. The slow files' .mathv stay valid so
        # make won't re-verify them.
        subprocess.run(
            ["make", "-j", "16", "library"],
            cwd=REPO_ROOT, capture_output=True, text=True,
        )
        for path in REPO_ROOT.glob("build/library/**/*.mathv"):
            rel = str(path.relative_to(REPO_ROOT))
            src = rel.replace("build/", "", 1).replace(".mathv", ".math")
            if src in SLOW_FILES:
                continue
            path.unlink()
    args = ["make", "-j", "16", "library"]
    if extra_flags:
        args.append(f"VERIFY_FLAGS={extra_flags}")
    return subprocess.run(args, cwd=REPO_ROOT, capture_output=True, text=True)


def collect_warnings(extra_flags=None, skip_slow=False):
    result = force_full_build(
        extra_flags=extra_flags, skip_slow=skip_slow)
    if result.returncode != 0:
        sys.stderr.write("baseline build failed:\n")
        sys.stderr.write(result.stderr or result.stdout)
        sys.exit(1)
    pattern = re.compile(
        r"warning:\s+([\w.]+):(\d+)(?::(\d+))?:\s+(.+)$"
    )
    seen = set()
    out = []
    for line in result.stdout.splitlines() + result.stderr.splitlines():
        m = pattern.search(line)
        if not m:
            continue
        module, lineno, col, message = (
            m.group(1), int(m.group(2)),
            int(m.group(3)) if m.group(3) else None,
            m.group(4),
        )
        file_path = REPO_ROOT / "library" / (module.replace(".", "/") + ".math")
        if not file_path.exists():
            continue
        key = (file_path, lineno, col, message)
        if key in seen:
            continue
        seen.add(key)
        out.append((file_path, lineno, col, message))
    return out


def strip_existing_markers(file_path: Path):
    """Drop any line that's only a `-- WARN:` marker."""
    text = file_path.read_text()
    out_lines = []
    for line in text.split("\n"):
        if line.lstrip().startswith(MARKER_PREFIX):
            continue
        out_lines.append(line)
    file_path.write_text("\n".join(out_lines))


def insert_markers(file_path: Path, warnings_for_file):
    """Insert one marker per warning, bottom-up by line number."""
    text = file_path.read_text()
    lines = text.split("\n")
    # Sort by line desc so earlier insertions don't shift later ones.
    by_line_desc = sorted(warnings_for_file, key=lambda w: -w[0])
    for lineno, col, message in by_line_desc:
        # lineno is 1-indexed; insert ABOVE this line, i.e. at index
        # (lineno - 1) in 0-indexed terms. Match the source line's
        # indentation so the marker doesn't break Python-ish parsers
        # (math files allow `--` anywhere).
        if lineno < 1 or lineno > len(lines):
            sys.stderr.write(
                f"  ! line {lineno} out of range for {file_path}\n"
            )
            continue
        target = lines[lineno - 1]
        # Indent = leading whitespace of the target line.
        indent_len = len(target) - len(target.lstrip())
        indent = target[:indent_len]
        col_text = f":{col}" if col else ""
        marker = f"{indent}{MARKER_PREFIX} (col{col_text}) {message}"
        lines.insert(lineno - 1, marker)
    file_path.write_text("\n".join(lines))


def main():
    flags = ["--check-redundant-by"]
    if "--calc-steps" in sys.argv:
        flags.append("--check-redundant-calc-steps")
    if "--non-eq" in sys.argv:
        flags.append("--check-redundant-by-non-eq")
    extra_flags = " ".join(flags)
    skip_slow = "--skip-slow" in sys.argv or "--non-eq" in sys.argv
    warnings = collect_warnings(
        extra_flags=extra_flags, skip_slow=skip_slow)
    print(f"{len(warnings)} warning(s) across "
          f"{len({w[0] for w in warnings})} file(s)")
    if not warnings:
        return 0
    # First pass: strip stale markers in every file we'll touch.
    touched = sorted({w[0] for w in warnings})
    for fp in touched:
        strip_existing_markers(fp)
    # Group by file, insert.
    by_file = {}
    for fp, ln, col, msg in warnings:
        by_file.setdefault(fp, []).append((ln, col, msg))
    for fp, lst in by_file.items():
        rel = fp.relative_to(REPO_ROOT)
        print(f"  inserting {len(lst)} marker(s) in {rel}")
        insert_markers(fp, lst)
    print("\nNow walk through each file's `-- WARN:` markers:")
    for fp in touched:
        print(f"  {fp.relative_to(REPO_ROOT)}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
