#!/usr/bin/env bash
#
# Frictionless error capture for the error-message corpus.
#
# Usage:
#   scripts/record_error.sh <file.math> [short note]
#
# Runs `kernel verify` on <file.math>, and appends a timestamped, raw
# capture (the command, the verbatim combined output, and a blank
# `diagnosis:`/`rubric:` to fill in later) to docs/error_message_inbox.md.
#
# The inbox is an APPEND-ONLY scratch log: capture now while the context
# is fresh, triage later. When an entry is understood, promote it into the
# curated docs/error_message_corpus.md (with a diagnosis + rubric score)
# and, once fixed, add a regression case under library/ErrorTest/.
#
# This deliberately does NOT assert success/failure — it just records what
# happened, for both error cases (the common use) and surprising successes.

set -u
cd "$(dirname "$0")/.."

if [ $# -lt 1 ]; then
  echo "usage: scripts/record_error.sh <file.math> [short note]" >&2
  exit 2
fi

file=$1
shift
note=${*:-}
inbox=docs/error_message_inbox.md
stamp=$(date '+%Y-%m-%d %H:%M:%S')

out=$( ( ulimit -t 90; ./kernel verify --source "$file" --cache-root build ) 2>&1 )
rc=$?

{
  echo ""
  echo "### $file — $stamp (exit $rc)"
  [ -n "$note" ] && echo "note: $note"
  echo '```'
  echo "\$ ./kernel verify --source $file --cache-root build"
  echo "$out"
  echo '```'
  echo "diagnosis: TODO — what was the *real* problem?"
  echo "rubric (0/1): cause · location · actionable · folded-types · no-jargon"
  echo ""
  echo "---"
} >> "$inbox"

echo "recorded → $inbox (exit $rc)"
