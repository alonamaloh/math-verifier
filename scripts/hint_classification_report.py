#!/usr/bin/env python3
"""Aggregate the B5 hint-classifier log into the Part-B sizing report.

Input: stderr of a library build run with MATH_CLASSIFY_HINTS=1, which
contains one tab-separated `[classify-hint]` line per hinted claim /
calc step (emitted by Elaborator::emitHintClassification).

Each record is assigned to ONE bucket, first match wins:

  closes-today     the budget-capped by-less re-proof already closes it
                   (today's redundancy checker would flag a `by`; for
                   `since` it means the hint is kept prose)
  B4-order-step    a hinted non-`=` calc step — the order-relation
                   rewrite-index extension's domain (plan B4)
  tier2-ground     no local variables: ground evaluation (plan tier 2)
  tier3+4-sign-cast sign judgment whose subject carries casts — cast
                   normalization then sign recursion (tiers 3 -> 4)
  tier4-sign       0-anchored sign/nonzero judgment (plan tier 4)
  tier3-cast       cast-bearing goal, not sign-shaped (plan tier 3)
  unabsorbed       none of the above: tier 0/5/6 or genuine content —
                   the hints that SHOULD stay on the page

Usage: scripts/hint_classification_report.py <classify_stderr.log>
"""

import collections
import sys


def parse(path):
    records = []
    seen = set()
    with open(path, errors="replace") as stream:
        for line in stream:
            if not line.startswith("[classify-hint]\t"):
                continue
            fields = line.rstrip("\n").split("\t")
            # [tag, module:line, kind=, rel=, since|by, closes=, neg=,
            #  head=, sign=, cast=, ground=, hint=, goal=]
            if len(fields) < 13:
                continue
            record = {"site": fields[1], "justifier": fields[4]}
            for field in fields[2:]:
                if "=" in field:
                    key, _, value = field.partition("=")
                    record[key] = value
            key = (record["site"], record.get("hint"), record.get("goal"))
            if key in seen:
                continue
            seen.add(key)
            records.append(record)
    return records


def bucket_of(record):
    if record.get("closes") == "1":
        return "closes-today"
    if record.get("kind") == "calc" and record.get("rel") != "=":
        return "B4-order-step"
    if record.get("ground") == "1":
        return "tier2-ground"
    if record.get("sign") == "1" and record.get("cast") == "1":
        return "tier3+4-sign-cast"
    if record.get("sign") == "1":
        return "tier4-sign"
    if record.get("cast") == "1":
        return "tier3-cast"
    return "unabsorbed"


BUCKET_ORDER = [
    "closes-today", "B4-order-step", "tier2-ground",
    "tier3+4-sign-cast", "tier4-sign", "tier3-cast", "unabsorbed",
]


def main():
    if len(sys.argv) != 2:
        sys.exit(__doc__)
    records = parse(sys.argv[1])
    if not records:
        sys.exit("no [classify-hint] records found")

    total = len(records)
    by_bucket = collections.defaultdict(list)
    for record in records:
        by_bucket[bucket_of(record)].append(record)

    since = sum(1 for r in records if r["justifier"] == "since")
    calc = sum(1 for r in records if r.get("kind") == "calc")
    print(f"hinted sites: {total}   "
          f"(since: {since}, by: {total - since}; "
          f"claims: {total - calc}, calc steps: {calc})\n")

    print(f"{'bucket':<20}{'count':>7}{'share':>8}")
    absorbed = 0
    for bucket in BUCKET_ORDER:
        count = len(by_bucket.get(bucket, []))
        if bucket != "unabsorbed":
            absorbed += count
        print(f"{bucket:<20}{count:>7}{count / total:>8.1%}")
    print(f"{'-- absorbable --':<20}{absorbed:>7}{absorbed / total:>8.1%}\n")

    for bucket in BUCKET_ORDER:
        group = by_bucket.get(bucket, [])
        if not group:
            continue
        print(f"== {bucket} ({len(group)}) ==")
        hints = collections.Counter(r.get("hint", "?") for r in group)
        for hint, count in hints.most_common(12):
            print(f"  {count:>5}  {hint}")
        goals = []
        for r in group:
            goal = r.get("goal", "")
            if goal and goal not in goals:
                goals.append(goal)
            if len(goals) == 3:
                break
        for goal in goals:
            print(f"       e.g. {goal[:110]}")
        print()

    directories = collections.Counter(
        r["site"].split(".")[0].split("/")[0].split(":")[0]
        for r in records)
    print("== sites per module root ==")
    for directory, count in directories.most_common(15):
        print(f"  {count:>5}  {directory}")


if __name__ == "__main__":
    main()
