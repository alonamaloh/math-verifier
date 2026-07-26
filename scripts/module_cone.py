#!/usr/bin/env python3
"""Print the transitive import cone of some modules, as .mathv targets.

Stage 2 (`X.mathv`, the proofs) depends on its imports' *interfaces*, not
their proofs — deliberately, so a proof-only edit elsewhere does not
re-verify you. The consequence is that asking make for one area's .mathv
never asks for its dependencies' .mathv at all.

That is the right trade for editing .math files. It is the wrong one after
a kernel or elaborator change, which invalidates every module's proofs:
the caches are correctly marked out of date (every .mathv depends on
`kernel`) but nothing in a narrow target ever requests them.

This walks build/library-depends.mk and prints the .mathv of every module
in the cone, so a target can request the proofs too.

    scripts/module_cone.py build/library-depends.mk build/library/Plane
"""

import sys


def main() -> int:
    if len(sys.argv) < 3:
        sys.stderr.write(__doc__)
        return 2
    depends_file, roots = sys.argv[1], sys.argv[2:]

    # `X.mathv.iface: A.mathv.iface B.mathv.iface ...`
    interface_imports: dict[str, list[str]] = {}
    try:
        with open(depends_file, encoding="utf-8") as handle:
            for line in handle:
                target, separator, prerequisites = line.partition(":")
                if not separator:
                    continue
                target = target.strip()
                if not target.endswith(".mathv.iface"):
                    continue
                interface_imports[target] = [
                    word
                    for word in prerequisites.split()
                    if word.endswith(".mathv.iface")
                ]
    except FileNotFoundError:
        # No dependency file yet: the caller's own files are the whole cone.
        pass

    pending = []
    for root in roots:
        pending.extend(
            interface
            for interface in interface_imports
            if interface.startswith(root)
        )

    reached: set[str] = set()
    while pending:
        interface = pending.pop()
        if interface in reached:
            continue
        reached.add(interface)
        pending.extend(interface_imports.get(interface, []))

    for interface in sorted(reached):
        print(interface[: -len(".iface")])
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
