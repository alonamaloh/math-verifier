#!/usr/bin/env python3
"""clean_status.py — dashboard + ratchet for the clean-style manifest.

`scripts/clean_manifest.txt` lists the files held to clean ("reads like math")
style. This script reports progress of that growing set toward the goal
theorems, each of which is GREEN once its whole import cone is in the manifest.

The goal set is the Freek-100 entries the library has verified, read straight
from the canonical index `docs/freek_100.md` (so the dashboard never goes stale
as new entries land), plus a couple of structural field milestones.

  scripts/clean_status.py                 # dashboard
  scripts/clean_status.py --ratchet N     # exit 1 if manifest residual leaks > N
  scripts/clean_status.py --gate <file>   # exit 1 unless that file's cone ⊆ manifest
"""
import re, os, json, subprocess, sys, argparse

def path_of(mod):
    return "library/" + mod.replace(".", "/") + ".math"

def cone(root):
    seen = set()
    def visit(p):
        if p in seen or not os.path.exists(p):
            return
        seen.add(p)
        for line in open(p):
            m = re.match(r'\s*import\s+([\w.]+)', line)
            if m:
                visit(path_of(m.group(1)))
    visit(root)
    return seen

# Structural milestones that are not Freek entries but anchor the manifest cones.
STRUCTURAL_MILESTONES = [
    ("ℚ is a field", ["library/Rational/field.math"]),
    ("ℝ is a field", ["library/Real/field.math"]),
]

def freek_milestones(index="docs/freek_100.md"):
    """Parse the Freek-100 index table into (label, [files]) milestones.

    Each row is `| # | theorem | declaration | file(s) |`; a row may name more
    than one file, in which case the milestone's cone is the union of theirs.
    """
    milestones = []
    for line in open(index):
        cells = [c.strip() for c in line.strip().strip("|").split("|")]
        if len(cells) < 4 or not cells[0].isdigit():
            continue
        number, theorem = cells[0], cells[1]
        files = re.findall(r'library/[\w/]+\.math', cells[-1])
        if files:
            milestones.append((f"#{number} {theorem}", files))
    milestones.sort(key=lambda m: int(m[0].split()[0][1:]))
    return milestones

def cone_of(roots):
    union = set()
    for root in roots:
        union |= cone(root)
    return union

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--ratchet", type=int)
    ap.add_argument("--gate")
    args = ap.parse_args()

    manifest = set(l.strip() for l in open("scripts/clean_manifest.txt")
                   if l.strip() and not l.startswith("#"))
    rep = json.loads(subprocess.check_output(["scripts/cic_leak_report", "--json"]))
    per = rep["per_file"]
    manifest_leaks = sum(sum(per[f].values()) for f in manifest if f in per)

    print(f"clean manifest: {len(manifest)} files, {manifest_leaks} residual leaks "
          f"(intended boundaries)\n")

    def report(title, milestones):
        print(f"{title:48s} {'cone':>5s} {'in set':>7s}  status")
        for name, roots in milestones:
            roots = [r for r in roots if os.path.exists(r)]
            if not roots:
                continue
            c = cone_of(roots)
            cov = len(c & manifest)
            status = "GREEN" if cov == len(c) else f"{100 * cov // len(c)}%"
            label = name if len(name) <= 48 else name[:45] + "..."
            print(f"{label:48s} {len(c):5d} {cov:7d}  {status}")

    report("Freek-100 theorem", freek_milestones())
    print()
    report("structural milestone", STRUCTURAL_MILESTONES)

    rc = 0
    if args.gate:
        missing = cone(args.gate) - manifest
        if missing:
            print(f"\ngate {args.gate}: NOT met — {len(missing)} cone files not in the "
                  f"clean manifest:")
            for m in sorted(missing):
                print("  " + m)
            rc = 1
        else:
            print(f"\ngate {args.gate}: met")
    if args.ratchet is not None and manifest_leaks > args.ratchet:
        print(f"\nratchet FAIL: manifest residual leaks {manifest_leaks} > budget "
              f"{args.ratchet}")
        rc = 1
    sys.exit(rc)

if __name__ == "__main__":
    main()
