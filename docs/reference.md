# Reference

A catalogue of surface constructs. For depth see `docs/conventions/`.

## Declarations

| Form | Meaning |
|---|---|
| `module M` | module header (first line after comments) |
| `import M` | bring another module's declarations into scope |
| `theorem N (params) : T := proof` | a proved fact |
| `definition N (params) : T := body` | a transparent definition (δ-unfolds) |
| `opaque definition N … ` | definition the kernel won't unfold; reason via its characterising lemmas |
| `inductive N (params) : Sort where \| C : … ` | an inductive type and its constructors |
| `axiom N : T` | assumed without proof |
| `operator (sym) on (T1, T2) := F` | infix/postfix operator dispatch |
| `E²` | parse-time sugar for `E * E` at any carrier (binds tighter than every binary operator: `2 * n²` is `2 * (n * n)`) |
| `instance N` | register the canonical structure instance/bundle for N's carrier |
| `coercion (S, T) := F` | canonical embedding S ↪ T |
| `congruence_under_binder F := L` | rewrite-under-binder lemma for head F |
| `fold_operation (sym) on T := W` | register `sym` on `T` as fold-capable; `W : IsMonoid(T, op, id)` must certify the same `op` the operator registry dispatches to (canonical per (sym, T); feeds the fold binder form and ellipsis notation) |
| `sum k from LO to HI of BODY` | Σ over the inclusive range as an ordinary term: `Algebra.Fold(carrier, +, 0, λk. BODY, LO, (1 + HI) ∸ LO)` via the fold_operation registry (monus-free count for literal LO ∈ {0,1}); `product … of …` is (*), `fold (op) k from … to … of …` any registered op; an upper bound written `E - 1` is half-open `[LO, E)` |
| `t₁ op … op ... op g` | ellipsis notation, sugar for the binder form: the general term `g` is the LAST term; index/term-function read by anti-unification against the last prefix term (fallback: 0/1 evaluation probe), prefix verified, mismatch/ambiguity are loud errors; `-` in the display is blackboard monus |
| `t₁ + … + g + ... = S` | trailing-ellipsis SERIES relation (one full side of an equality only): elaborates to `Real.SequenceConverges(λN. partial folds, S)`; `= infinity` gives `Real.TendsToInfinity`; sums at Real, first index 0/1; term-position/inequality uses are errors |

Pattern-match definition: `definition f : A → B \| pat1 => e1 \| pat2 => e2`.

## Types & propositions

`Natural`, `Integer`, … ; `Proposition`; `Type(0)`, `Type(1)`, … .
Function/Pi: `(x : T) → U`, or `A → B` when non-dependent.
Logic: `P ∧ Q`, `P ∨ Q`, `¬P`, `∃ (x : T). P`, `a = b`.
Order/divisibility notation: `≤`, `<`, `≥`, `>`, `∣` (these are inductive
or defined; they print and parse infix).
Numerals: write `0`/`1`/`2`, and `1 + n` rather than `successor(n)` in
expressions (kernel-defeq; pattern positions keep `successor`).

## Proof terms

| Form | Meaning |
|---|---|
| `f(a, b)` | application |
| `(x : T) ↦ e` | lambda (also `(x : T)(y : U) ↦ e`) |
| `⟨a, b, c⟩` | anonymous tuple — `∧`-intro / `∃`-intro (right-nested) |
| `reflexivity(x)` | `x = x` |
| `absurd(p)` | from a proof of an impossible/`False` fact, prove anything; `p` may be a **proposition** (proved from context, then contradicted) |
| `witness w with proof` | prove `∃ x. P(x)` |

## calc

```
calc a   = b   by L         -- '=' step needs the lemma applied (diff-inference)
       ≤ c                  -- '≤'/'∣' step: argument-free `by L`, or by-less
       < d   by R      as NAME
```
- Mixed relations compose (`=`,`≤`,`<`,`≥`,`>`,`∣`).
- A by-less step is closed by the auto-prover.
- `by L` justifies a step. `as NAME` binds the step's fact.
- `substituting eq` / `rewrite(eq)` rewrite by an equality (prefer
  `substituting`; raw `rewrite` is a counted CIC leak). `eq` may be a
  proof, a proposition (`substituting (x = head)` — proved in place), or
  a quantified lemma cited by name (`substituting Natural.add_zero` —
  arguments inferred by matching its conclusion against the goal).

## Claims & closers

| Form | Meaning |
|---|---|
| `claim P;` | assert `P`, auto-proved |
| `P;` / `P by V;` / `P as NAME;` | **keyword-free claim** (A1): a bare stated proposition (or proof term) at statement position is a claim — verified, then in scope. A block may end by restating the goal. The final expression (`E}` or `E;}`) keeps its ordinary meaning |
| `claim <proofTerm>;` | the argument is a **proof** (a hypothesis / cited lemma) — claim its *type* as the fact, no type restated (mirror of the proposition-as-proof coercion) |
| `claim P by V;` | assert `P`, discharged by `V` |
| `claim NAME : P [by V];` | named (reference `NAME` later) |
| `claim P by cases { case A as h: … case B as h: … }` | prove `P` by ∨-elimination |
| `P by cases { case A: … otherwise [as h]: … }` | last-arm `otherwise:` covers the complement `¬(A ∨ …)`; exhaustiveness is excluded middle by construction, never a prover obligation |
| `case n = k + 1 for some k [as eq]:` | structural case: the arm's hypothesis is `∃ k. n = k + 1`, with the witness `k` and the equation both in scope in the body (`as` names the equation). Witness type inferred from the equation's left side; annotate with `for some (k : T)` otherwise. Exhaustiveness discharges through the coverage lemma (`Natural.zero_or_add_one` / `zero_or_one_plus` are automatic). **Substitution rule**: the arm's goal has `n` substituted by `k + 1` (transported back automatically), so the kernel ι-reduces on the constructor form — state computed facts bare, no `by substitution` plumbing |
| `claim P by substituting eq;` | prove `P` by rewriting with `eq` |
| `claim goal [by V]` | close the current goal (type from context) |
| `done` / `okay` | ≡ `claim goal`; bare or with `by` |
| `theorem X : T := by L` | the whole proof is a citation of `L`; the prover does the logical plumbing (premise discharge, `Or.self` collapse) |
| `note P [by V];` | a *checked comment*: verify `P` holds, then **discard** it — unlike `claim`, it does NOT bind `P`, so later steps don't see it |
| `note goal : T;` | a checked assertion that the goal is (defeq) `T`; non-binding, goal unchanged |
| `change T;` | replace the goal by a defeq `T` (this *does* change the proof state) |

`goal` is the *name* of the current goal type (used in `claim goal`,
`note goal : T`); it is not a standalone proof.

## Induction & cases

```
by induction on x with IH { case x = 0: … case x = k + 1 for some k: … }
by induction on x { case x = 0: … case x = k + 1, with IH: … }  -- header-less: arms name their own IH
by induction on x with IH { case zero: … case successor(k): … } -- constructor-pattern arms
by induction on x with IH generalizing b, … { … }  -- induction loading: IH quantifies over b (scrutinee-dependent hypotheses generalise automatically)
by induction on x using R with subject, IH { … }   -- with an explicit recursor
by strong induction on n with hypothesis IH { … }  -- subject shadows n; IH : (k) → k < n → P(k)
by strong induction on n with hypothesis IH;       -- statement form: the REST of the block is the body (no braces)
by strong induction on n with subject, IH { … }    -- explicit subject name (needed when `on` isn't a plain variable)

cases e { | pat => … }                 -- split an inductive value
cases e with eq { | pat => … }         -- also bind eq : e = pat
cases by L { | C(args) => … }          -- split a lemma's disjunction (args inferred)
if P then a else b                     -- value-level classical conditional (cases on `Logic.classical_decidable(P)`)
```
`if P then a else b` branches a definition on any proposition `P` — a
mathematical condition, not a constructor pattern. Reason about the result
through the generic characterizing equations `Logic.if_positive` /
`Logic.if_negative` (each conditional definition states its own equations as
one-liner corollaries; see `Rational.minimum_eq_left`). It is
non-computational (goes through `classical_decidable`), so it defines and
proves but does not reduce on closed inputs. The old proof-side
`decide P { yes/no }` construct is retired — classical splits in proofs are
`by cases { case P: … otherwise: … }`.
Inside `by induction`, the recursion is the local hypothesis `IH`; apply it
(`IH(args)`) — not a lemma call. The header `with IH` is optional when the
recursive arms name their own hypothesis (`case x = k + 1, with IH:`); the
old `by_induction`/`by_strong_induction` spellings are retired.

## Hypothesis introduction (block statements)

End each with `;`; the block returns its final non-`;` expression.

| Form | Meaning |
|---|---|
| `take x : T;` | introduce a ∀-bound variable |
| `suppose P as h;` | introduce a hypothesis |
| `suppose Not(G) [as h] for contradiction;` | reductio (terminal): assume `Not(G)`, derive `False` in the continuation, prove the goal `G` by double-negation elimination |
| `suppose Not(X) [as h] for contradiction { … };` | reductio (forward): the braced block derives `False`, establishing `X` into the context, then the proof continues at the original goal |
| `suppose P [as h] for proving Q { … };` | forward implication: prove `Q` under `h : P`, adding `P → Q` to the context for the rest of the block |
| `take x : T for proving Q { … };` | forward ∀-introduction: prove `Q` under `x : T`, adding `∀ (x : T). Q` to the context for the rest of the block |
| `choose w [such that P] [as h] from S;` | `∃`-elimination (preferred): `S` a hypothesis, a lemma cited argument-free, or an applied term |
| `choose n such that P(n);` | `∃`-elimination from the most-recent in-scope `∃` |
| `choose m, n such that P;` | witness list — flattens a nested `∃` (with an `∧`-chain under the innermost binder) in one step |
| `eventually (m). P(m)` | "P holds from some index on" — `Natural.Eventually((m : Natural) ↦ P(m))`; combine via `Eventually.and` (max of thresholds) / `Eventually.monotone`; `choose N such that … from h` opens the threshold |
| `eventually (m): { … }` / `for sufficiently large m: { … }` | proves an eventual goal: every in-scope `eventually`-fact is usable at `m` (thresholds combined invisibly); the body proves the goal's property at `m` |
| `suffices Q by <reduction>;` | changes the goal (backward): the rest of the block proves `Q`, and `<reduction> : Q → goal` closes the original |
| `suffices Q by definition of X[, Y];` | `Q` is the goal with the named definition(s) unfolded — no reduction lemma; carries the definitional step even when `X` is opaque |
| `let ⟨a, b⟩ := E;` | tuple destructure — genuine data records only (`∃`/`∧` → use `choose`; `obtain` is retired) |
| `take x as representative(a, b) : T;` / `cases x { \| representative(a, b) => … }` | quotient destructure — the carrier's constructor is resolved from the type, never written |
| `let x := V;` / `set x := V;` | local (transparent) binding |

## Tactics

`ring` — commutative-ring identities. `field(h, …)` — fields/reciprocals.
`linear_combination …` — prove an equality as a combination of hypotheses.

## Inference & citation

- `by L` (argument-free): cite lemma `L`; its explicit
  arguments are inferred from the goal and premises discharged from
  context. Use this instead of applying `L` to positional arguments.
- **Statement addressing (A2)**: a PROPOSITION in function position —
  `(∀ (k : Natural). P(k))(m)` — or as a `choose` source addresses
  the in-scope fact with that statement (defeq match, anonymous facts
  included); two matching facts is a loud error naming both. `given (P)`
  is the same lookup as a bare term. Inside a `cases x with eq` arm,
  addressing the REFINED statement (`P(successor(k))` when the context
  holds `P(x)`) transports silently along the case equation
  (single-position shapes).
- `?` — a hole in a function-call argument position, solved by unification
  from the goal/other arguments (does not invoke the auto-prover).
- `recalling f, g` after a `by` hint — bring extra named facts into
  the discharge scope.
- A context hypothesis `A ∧ B` makes both `A` and `B` available as facts
  (conjunction-elimination, recursive) — no manual `And.left`/`And.right`.
- `{x : T}` — an implicit parameter, solved by unification at call sites.
