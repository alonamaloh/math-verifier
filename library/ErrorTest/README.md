# Expected-error tests

Every `.math` file here is intentionally invalid. Its matching `.expected`
file records the diagnostic that verification must produce; occasional `.flags`
files add verifier options. Run the suite with `make error-tests`.

## What belongs here

- Invalid theorem citations, ambiguous premises, and failed substitutions
- Retired syntax with a migration diagnostic
- Unsupported or ill-typed operators, folds, patterns, and induction forms
- Interface sealing and implementation errors
- Error-location and goal-display regressions

Keep each fixture focused on one failure. The `.math` filename and
`.expected` filename must match, and expected text should assert the useful
diagnostic rather than incidental internal details. Successful counterparts
belong in [`../Test/README.md`](../Test/README.md).
