# Style guide

The standard is simple: a proof should read like mathematics, with the
kernel checking it. The files in `scripts/clean_manifest.txt` are the best
current examples.

## Start from the public interface

Read `library/<Area>/README.md` before using an area. Prefer its named
definitions and theorems to representation details.

Outside `Natural/`, use `ℕ`, numerals, and arithmetic. Do not use
`zero`, `successor`, `Natural.Raw`, constructor patterns, or the raw
recursor. Write `n + 1` or `1 + n` and use equation-shaped cases and
induction.

Do not unfold an opaque abstraction in consumer code. If its public
interface is missing a useful characterization, add that boundary theorem.

## State the mathematics

Use a relation chain when the argument is transitivity, rewriting, or
calculation:

```math
first
   = middle by reason
   ≤ last
```

Inside a proof block, state intermediate propositions directly:

```math
P;
Q by theoremName;
```

Name a fact with `as name` only when later text explicitly uses the name.
Anonymous facts remain available by their propositions.

## Let inference remove plumbing

Try a by-less fact or chain step first. The prover uses local hypotheses,
`automatic` declarations, and its built-in equality, order, sign, and
algebra reasoning.

When help is needed, cite the operative theorem without positional proof
arguments:

```math
desiredFact by ImportantTheorem;
```

Avoid:

```math
ImportantTheorem(a, b, premise)
```

unless an argument is genuine mathematical data that cannot be inferred.

For commutative-ring identities, try `ring` first. For field identities
with division, try `field(nonzeroFacts...)`.

## Use the proof structure that matches the argument

- Universal statement: `take`.
- Implication: `suppose`.
- Existential introduction: `witness`.
- Existential elimination: `choose`.
- Inductive argument: `by induction`.
- Structural alternatives: equation-shaped `done by cases`.
- Classical condition: `done by cases { case P: ... otherwise: ... }`.
- Conditional data: `if P then ... else ...`.
- Contradiction: `suppose ... for contradiction` or a directly stated
  impossible fact followed by `done`.

Raw scrutinee pattern splitting is not part of the proof language. Use the
equation-shaped alternatives, induction, or the public data-destructuring
form for the type.

## Keep logical connectives mathematical

Do not expose the tuple encoding of `∧` and `∃`.

- Build `A ∧ B` by establishing `A`, then `B`, then `done`.
- Use a conjunction by stating the needed leg.
- Build `∃ x. P(x)` with `witness`.
- Use it with `choose`.
- Prove `A ∨ B` by establishing the true side and closing.
- Eliminate a disjunction with `done by cases`.

Tuple syntax remains appropriate for genuine data records.

## Prefer readable local structure

Use `let` for a long expression repeated several times. Keep a coercion or
type ascription visible at one binding rather than repeating it throughout a
chain.

Use descriptive declared names. Long qualified names are searchable.
Short conventional local variables such as `i`, `n`, or `x` are fine.

Wrap at roughly 140 columns, but do not create unnecessary vertical sprawl.

## Comments explain strategy, not steps

The proof text should say what each mathematical step establishes. A comment
that merely paraphrases the next line is evidence that the line should be
made clearer.

A short comment may explain a non-obvious strategy. Representation or
elaborator mechanics belong only in foundational implementation code and
should be marked as an implementation note.

## Separate construction from use

A clean abstraction file normally has:

1. a representation or construction;
2. characterizing boundary theorems;
3. representation-level proofs kept close to the construction;
4. thin public adapters;
5. consumer theorems written entirely through the public interface.

Do not let quotient, subtype, raw-constructor, or transport machinery leak
into ordinary mathematical results.

## Check the result

Build the library:

```sh
make -j 16 library
```

For language and elaborator work:

```sh
make -j 16 tests
```

For files in the clean manifest:

```sh
make clean-check
make clean-anon-ratchet
```

The redundancy checks can find removable hints and unused names, but their
output is a polishing aid rather than a substitute for reading the proof.
The final test is whether the proof communicates the mathematical argument.
