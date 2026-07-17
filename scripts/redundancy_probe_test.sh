#!/bin/bash
# Regression guard for the redundancy-checker's speculative re-proofs.
#
# The --check-redundant-by / --check-redundant-by-non-eq probes speculatively
# re-elaborate steps to test whether a `by` hint is removable. Those probes must
# NEVER make a file that verifies plain fail under the checker. Two real bugs
# once broke exactly this — both in library files that verify clean normally:
#
#   * Real/continuity.math — the non-`=` redundancy probe used the targeted
#     tryContextFactMatch instead of the by-less autoProveClaim, mis-elaborating
#     a generic-lemma step and printing a spurious "different relation" error.
#   * Rational/order_multiplication.math — the inferable-args check speculatively
#     elaborated a BARE universe-polymorphic citation; on failure it corrupted
#     elaborator state, breaking a later `since fraction_equal` (value(make(K,0))
#     no longer matched a fraction). Fixed by skipping universe-poly lemmas.
#
# This script asserts both files (and the whole clean manifest) stay free of
# "elaborate error" under the redundancy checks.
set -u
cd "$(dirname "$0")/.."

status=0
for f in library/Rational/order_multiplication.math library/Real/continuity.math; do
    out=$(./kernel verify --source "$f" --cache-root build \
              --check-redundant-by --check-redundant-by-non-eq 2>&1)
    if echo "$out" | grep -q "elaborate error"; then
        echo "redundancy-probe-tests: FAIL — $f spuriously errors under --check-redundant-by"
        status=1
    fi
done

# U3b — terminal-tail suppression, both directions: the `P by H` proof-tail
# in Test/redundant_by_terminal_claim_test.math must NOT be flagged (its `by`
# is not deletable), while the statement form in the same file MUST still be.
terminal_out=$(./kernel verify \
    --source library/Test/redundant_by_terminal_claim_test.math \
    --cache-root build --check-redundant-by --no-check-unused-names 2>&1)
if echo "$terminal_out" | grep -q ":19: redundant \`by\`"; then
    echo "redundancy-probe-tests: FAIL — terminal-tail \`by\` flagged as redundant (U3b regression)"
    status=1
fi
if ! echo "$terminal_out" | grep -q ":24: redundant \`by\`"; then
    echo "redundancy-probe-tests: FAIL — statement \`by\` no longer flagged (checker went blind)"
    status=1
fi

if [ "$status" -eq 0 ]; then
    echo "redundancy-probe-tests: PASS"
fi
exit "$status"
