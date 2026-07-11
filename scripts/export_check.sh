#!/usr/bin/env bash
# export-check — PLAN_KERNEL_EXPORT Stage 4.
#
# Builds the full-library lean4export NDJSON trail, replays it through an
# independent Lean-kernel checker (nanoda), and asserts the trail's axiom
# report EXACTLY equals the documented inventory
# (docs/kernel-export-axiom-inventory.md) — a stray axiom, a `sorry`, or
# a dropped axiom all fail loudly.
#
# Usage: scripts/export_check.sh <kernel-binary> <output-dir> [nanoda-bin]

set -u

KERNEL="${1:?kernel binary}"
OUTDIR="${2:?output dir}"
NANODA="${3:-$HOME/claude/export-tools/nanoda_bin}"

if [ ! -x "$NANODA" ]; then
    echo "export-check: nanoda binary not found at $NANODA" >&2
    echo "  build it from https://github.com/ammkrn/nanoda_lib" \
         "(cargo build --release --bin nanoda_bin) and pass its path" >&2
    exit 1
fi

mkdir -p "$OUTDIR"
TRAIL="$OUTDIR/library.ndjson"
CONFIG="$OUTDIR/nanoda-config.json"
REPORT="$OUTDIR/nanoda-report.txt"

# The documented axiom inventory — keep in lockstep with
# docs/kernel-export-axiom-inventory.md.
EXPECTED_AXIOMS="Equality.propositional_extensionality
Logic.excluded_middle
Logic.the
Logic.the_satisfies
Quot.sound"

ROOTS=$(find build/library -name '*.mathv' \
        -not -path '*/Test/*' -not -path '*/ErrorTest/*' | sort)
# shellcheck disable=SC2086
"$KERNEL" export-lean4 --output "$TRAIL" $ROOTS \
    || { echo "export-check: exporter FAILED"; exit 1; }

cat > "$CONFIG" <<EOF
{
    "export_file_path": "$TRAIL",
    "use_stdin": false,
    "permitted_axioms": ["Equality.propositional_extensionality",
                         "Logic.excluded_middle", "Logic.the",
                         "Logic.the_satisfies", "Quot.sound"],
    "unpermitted_axiom_hard_error": true,
    "nat_extension": true,
    "string_extension": false,
    "pp_declars": [],
    "pp_to_stdout": true,
    "print_success_message": true
}
EOF

"$NANODA" "$CONFIG" > "$REPORT" 2>&1 \
    || { echo "export-check: external checker FAILED:";
         tail -5 "$REPORT"; exit 1; }

# Exact axiom-report assertion. nanoda prints every admitted axiom as
# `axiom <Name>[.{levels}] ...`; strip to the bare name and compare.
ACTUAL_AXIOMS=$(grep '^axiom ' "$REPORT" | awk '{print $2}' \
                | sed 's/\.{.*//' | sort)
if [ "$ACTUAL_AXIOMS" != "$(printf '%s\n' "$EXPECTED_AXIOMS" | sort)" ]; then
    echo "export-check: axiom report does NOT match the documented inventory"
    echo "--- expected:"; printf '%s\n' "$EXPECTED_AXIOMS" | sort
    echo "--- actual:";   printf '%s\n' "$ACTUAL_AXIOMS"
    exit 1
fi

CHECKED=$(grep -o 'Checked [0-9]* declarations with no errors' "$REPORT")
echo "export-check: PASS — $CHECKED; axiom report matches the inventory"
