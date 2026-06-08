# Error-message inbox (append-only capture log)

Raw, untriaged captures of error messages we hit while working — recorded
by `scripts/record_error.sh <file.math> [note]` so nothing is lost while
the context is fresh. This file is a SCRATCH log, not a curated document.

Workflow:
1. Hit a confusing (or surprisingly good) error → `scripts/record_error.sh
   path/to/repro.math "what I was trying to do"`. It appends the verbatim
   output plus a blank `diagnosis:` here.
2. When you understand it, **promote** it into
   `docs/error_message_corpus.md` (diagnosis + 5-axis rubric score +
   status), and delete the inbox entry.
3. When fixed, add a regression case under `library/ErrorTest/` and run
   `make error-tests`.

Keep entries here only until triaged — the corpus is the durable record.

<!-- captures are appended below this line -->
