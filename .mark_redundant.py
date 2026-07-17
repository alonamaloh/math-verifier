#!/usr/bin/env python3
"""Settle the mechanical redundancy categories, then mark the judgment ones.

Runs the kernel's `--check-redundant-by` and `--check-redundant-calc-steps`
diagnostics on each given .math file. Two warning categories need no human
judgment (U6), so they are APPLIED directly rather than marked:

  * `unused name ‹X›` / `calc ... as X is never textually referenced` —
    the name is never typed downstream (the fact itself stays load-bearing
    via type-match), so the ` as X` postfix is dropped.
  * a redundant `by Logic.excluded_middle` — the auto-prover reaches for
    excluded middle itself; the hint is pure noise.

Settled edits are verified as a batch: the file is re-verified after
application, and on ANY failure the original text is restored and every
site falls back to marking (the checker pre-verifies each suggestion in
isolation — U3 — but adjacent edits in a chain can still interact).

Every remaining warning is appended to its source line as a marker comment
carrying the EXACT warning text the kernel emitted (wrapped in `«…»`), so
the fix instructions travel with the marker — no need to recall what a
terse tag like `UNUSED-NAME` was shorthand for. (That shorthand is what
led to whole claims being deleted when only the *name* was redundant.)
Markers are inserted in descending line order so earlier insertions never
shift the line numbers of later ones. A human (or a lesser LLM) applies
the flagged fix BY HAND, rebuilds, and reverts anything that turns out to
be a false positive.

Usage:  python3 .mark_redundant.py library/Foo/bar.math [more.math ...]
        python3 .mark_redundant.py --no-settle library/Foo/bar.math  # mark only
        python3 .mark_redundant.py --unmark library/Foo/bar.math     # strip markers
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

# The two auto-settled categories (U6). Anything else is a judgment call.
UNUSED_NAME_RE = re.compile(r"unused name `([^`]+)`")
CALC_AS_RE = re.compile(r"`calc \.\.\. as ([^`]+)` is never textually referenced")
REDUNDANT_BY_RE = re.compile(r"redundant `by` on ")
EXCLUDED_MIDDLE_HINT_RE = re.compile(r"[ \t]+by[ \t]+Logic\.excluded_middle\b")

# How far past the warning line to look for the statement's ` as X` /
# `by Logic.excluded_middle` tail (multi-line statements put it on its own
# continuation line). The final re-verify catches any mis-fire.
SETTLE_SCAN_LINES = 40


def run_verify(path, check_flags):
    out = f"/tmp/mark_{os.getpid()}.mathv"  # unique per process for -P safety
    result = subprocess.run(
        ["./kernel", "verify", "--source", path, "--output", out,
         "--cache-root", "build"] + check_flags,
        capture_output=True, text=True)
    try:
        os.remove(out)
    except OSError:
        pass
    return result


def run_check(path):
    """Run all three redundancy diagnostics in one pass (cost-limited)."""
    result = run_verify(path, ["--check-redundant-by",
                               "--check-redundant-by-non-eq",
                               "--check-redundant-calc-steps"])
    return result.stdout + result.stderr


def collect(path):
    """Return {line_number: [messages]} — every distinct warning per line.

    The settle pass considers them all (a line can carry both a redundant-`by`
    and an unused-name warning); the marking pass keeps only the first — a
    marker lives at the end of its source line, so a line carries exactly one.
    """
    marks = {}
    for line in run_check(path).splitlines():
        m = WARNING_RE.match(line)
        if not m:
            continue
        messages = marks.setdefault(int(m.group(1)), [])
        if m.group(2).strip() not in messages:
            messages.append(m.group(2).strip())
    return marks


def remove_match(lines, index, regex):
    """Drop regex's first match from lines[index]; tidy the remainder.

    Returns True if something was removed. A line left holding only
    whitespace (or whitespace + `;`/`}`-tail) is merged onto the previous
    nonblank line so multi-line statements stay well-formed.
    """
    text = lines[index].rstrip("\n")
    new_text, n = regex.subn("", text, count=1)
    if n == 0:
        return False
    if new_text.strip() == "":
        del lines[index]
    elif new_text.strip() in {";", ";}", "; }"} and index > 0:
        lines[index - 1] = lines[index - 1].rstrip("\n") + new_text.strip() + "\n"
        del lines[index]
    else:
        lines[index] = new_text + "\n"
    return True


DECLARATION_RE = re.compile(
    r"^\s*(theorem|definition|automatic|opaque|module|import|instance|"
    r"convention|operator|--)\b")


def try_settle_site(lines, line_number, message):
    """Apply one auto-settled edit near line_number. Returns a label or None."""
    start = line_number - 1
    if start < 0 or start >= len(lines):
        return None
    stop = min(len(lines), start + SETTLE_SCAN_LINES)
    m = UNUSED_NAME_RE.search(message) or CALC_AS_RE.search(message)
    if m:
        as_re = re.compile(r"[ \t]+as[ \t]+" + re.escape(m.group(1)) + r"\b")
        for i in range(start, stop):
            if i > start and DECLARATION_RE.match(lines[i]):
                return None  # ran into the next declaration: no ` as X` tail
            if remove_match(lines, i, as_re):
                return f"dropped ` as {m.group(1)}`"
        return None
    if REDUNDANT_BY_RE.search(message):
        # Only this site's own hint may be dropped: stop at the first line
        # carrying a `by` (that IS the hint — matching or not) or ending the
        # statement, so a later statement's excluded-middle hint — possibly
        # unflagged — is never touched.
        for i in range(start, stop):
            if remove_match(lines, i, EXCLUDED_MIDDLE_HINT_RE):
                return "dropped `by Logic.excluded_middle`"
            if re.search(r"\bby\b", lines[i]) or ";" in lines[i]:
                return None
        return None
    return None


def settle(path, marks):
    """Apply the mechanical categories; verify the batch; revert on failure.

    Returns the set of settled line numbers (empty if nothing applied or the
    batch failed verification).
    """
    with open(path) as f:
        original = f.readlines()
    lines = original[:]
    settled = {}
    for line_number in sorted(marks, reverse=True):  # later first: no shifts
        for message in marks[line_number]:
            label = try_settle_site(lines, line_number, message)
            if label:
                settled.setdefault(line_number, []).append(label)
    if not settled:
        return {}
    with open(path, "w") as f:
        f.writelines(lines)
    check = run_verify(path, [])
    if check.returncode != 0:
        with open(path, "w") as f:
            f.writelines(original)
        print(f"{path}: auto-settle batch failed verification — reverted, "
              f"falling back to marking all sites")
        return {}
    return settled


def unmark(path):
    with open(path) as f:
        lines = f.readlines()
    out = [MARK_RE.sub("", ln.rstrip("\n")) + "\n" for ln in lines]
    with open(path, "w") as f:
        f.writelines(out)


def mark(path, do_settle=True):
    marks = collect(path)
    if not marks:
        print(f"{path}: clean")
        return
    if do_settle:
        settled = settle(path, marks)
        if settled:
            for ln in sorted(settled):
                print(f"{path}:{ln}: settled — {', '.join(settled[ln])}")
            # Line numbers moved; re-collect for the marking pass.
            marks = collect(path)
            if not marks:
                print(f"{path}: clean after settling {len(settled)} site(s)")
                return
    with open(path) as f:
        lines = f.readlines()
    for line_number in sorted(marks, reverse=True):  # later first
        index = line_number - 1
        if 0 <= index < len(lines):
            stripped = lines[index].rstrip("\n")
            if not MARK_RE.search(stripped):
                lines[index] = stripped + "  -- «" + marks[line_number][0] + "»\n"
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
        do_settle = True
        if args and args[0] == "--no-settle":
            do_settle = False
            args = args[1:]
        for p in args:
            mark(p, do_settle)
