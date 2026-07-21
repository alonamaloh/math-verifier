# Successful verification tests

This directory contains small `.math` programs that must verify successfully.
They exercise surface syntax, elaboration, inference, tactics, operators,
coercions, interfaces, and library integration. They are not imported by the
mathematics library and are built by `make -j 16 tests`, not by the faster
`make -j 16 library` target.

## Finding an example

Filenames are the index. Useful families include:

- `calc_*`, `substituting_*`, `choose_*`, `take_*`, and `suppose_*` for proof
  syntax
- `induction_*`, `strong_induction_*`, `well_founded_*`, and
  `named_recursion_*` for recursion
- `citation_*`, `lemma_index_test`, `backward_chaining_test`, and
  `diff_*` for theorem search and inference
- `ring_*`, `field_*`, `lincomb_test`, and `module_tactic_test` for algebra
  tactics
- `disjunct_test` for compact, explicit injection into disjunction chains
- `coercion_*`, `cast_*`, `numeral_*`, and `operator_*` for elaboration
- `quotient_*`, `interface_*`, and `implementation_module_test` for module and
  abstraction boundaries
- `vector_*`, `matrix_*`, `span_test`, `complex_*`, and `integer_mod_test` for
  worked library examples

When adding or fixing a language feature, prefer the smallest test that isolates
the behavior. A test should demonstrate the accepted spelling; rejected
spellings and diagnostic text belong in `ErrorTest/`.
