#!/usr/bin/env python3
"""clean_status.py — dashboard + ratchet for the clean-style manifest.

`scripts/clean_manifest.txt` lists the files held to clean ("reads like math")
style. This script reports progress of that growing set toward the milestone
theorems (FTA → ℚ-field → ℝ-field → IVT), each of which is GREEN once its whole
import cone is in the manifest.

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

MILESTONES = [
    ("FTA (unique factorization)", "library/Algebra/unique_factorization.math"),
    ("Q is a field",               "library/Rational/field.math"),
    ("R is a field",               "library/Real/field.math"),
    ("IVT",                        "library/Real/intermediate_value.math"),
]

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
    print(f"{'milestone':30s} {'cone':>5s} {'in set':>7s}  status")
    for name, root in MILESTONES:
        if not os.path.exists(root):
            continue
        c = cone(root)
        cov = len(c & manifest)
        status = "GREEN" if cov == len(c) else f"{100 * cov // len(c)}%"
        print(f"{name:30s} {len(c):5d} {cov:7d}  {status}")

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
