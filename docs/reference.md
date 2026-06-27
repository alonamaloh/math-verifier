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
       < d   since R   as NAME
```
- Mixed relations compose (`=`,`≤`,`<`,`≥`,`>`,`∣`).
- A by-less step is closed by the auto-prover.
- `by L` justifies a step; `since R` is the same but kept as explanation
  (exempt from the redundant-`by` lint). `as NAME` binds the step's fact.
- `substituting eq` / `rewrite(eq)` rewrite by an equality (prefer
  `substituting`; raw `rewrite` is a counted CIC leak). `eq` may be a
  proof, a proposition (`substituting (x = head)` — proved in place), or
  a quantified lemma cited by name (`substituting Natural.add_zero` —
  arguments inferred by matching its conclusion against the goal).

## Claims & closers

| Form | Meaning |
|---|---|
| `claim P;` | assert `P`, auto-proved |
| `claim <proofTerm>;` | the argument is a **proof** (a hypothesis / cited lemma) — claim its *type* as the fact, no type restated (mirror of the proposition-as-proof coercion) |
| `claim P by V;` / `claim P since V;` | assert `P`, discharged by `V` |
| `claim NAME : P [by V];` | named (reference `NAME` later) |
| `claim P by cases { in A as h: … in B as h: … }` | prove `P` by ∨-elimination |
| `claim P by substituting eq;` | prove `P` by rewriting with `eq` |
| `claim goal [by V]` | close the current goal (type from context) |
| `done` / `okay` | ≡ `claim goal`; bare or with `by`/`since` |
| `note P [by V];` | a *checked comment*: verify `P` holds, then **discard** it — unlike `claim`, it does NOT bind `P`, so later steps don't see it |
| `note goal : T;` | a checked assertion that the goal is (defeq) `T`; non-binding, goal unchanged |
| `change T;` | replace the goal by a defeq `T` (this *does* change the proof state) |

`goal` is the *name* of the current goal type (used in `claim goal`,
`note goal : T`); it is not a standalone proof.

## Induction & cases

```
by_induction on x with IH { case zero: … case successor(k): … }
by_induction on x with IH refining h, … { … }      -- generalise h per case
by_induction on x using R with subject, IH { … }   -- with an explicit recursor
by_strong_induction on n with subject, IH { … }    -- IH : (k) → k < n → P(k)

cases e { | pat => … }                 -- split an inductive value
cases e with eq { | pat => … }         -- also bind eq : e = pat
cases e refining h { | pat => … }      -- generalise scrutinee-dependent h
cases by L { | C(args) => … }          -- split a lemma's disjunction (args inferred)
decide P { | yes m => … | no n => … }  -- classical Type-valued case-split
```
Inside `by_induction`, the recursion is the local hypothesis `IH`; apply it
(`IH(args)`) — not a lemma call.

## Hypothesis introduction (block statements)

End each with `;`; the block returns its final non-`;` expression.

| Form | Meaning |
|---|---|
| `take x : T;` | introduce a ∀-bound variable |
| `suppose P as h;` | introduce a hypothesis |
| `suppose Not(G) [as h] for contradiction;` | reductio (terminal): assume `Not(G)`, derive `False` in the continuation, prove the goal `G` by double-negation elimination |
| `suppose Not(X) [as h] for contradiction { … };` | reductio (forward): the braced block derives `False`, establishing `X` into the context, then the proof continues at the original goal |
| `suppose P [as h] to prove Q { … };` | forward implication: prove `Q` under `h : P`, adding `P → Q` to the context for the rest of the block |
| `choose w [such that P] [as h] from S;` | `∃`-elimination (preferred): `S` a hypothesis, a lemma cited argument-free, or an applied term |
| `choose n such that P(n);` | `∃`-elimination from the most-recent in-scope `∃` |
| `obtain ⟨a, b⟩ from E;` / `let ⟨a, b⟩ := E;` | tuple destructure — non-existential structures only (`∃`/`∧` → use `choose`) |
| `let x := V;` / `set x := V;` | local (transparent) binding |

## Tactics

`ring` — commutative-ring identities. `field(h, …)` — fields/reciprocals.
`linear_combination …` — prove an equality as a combination of hypotheses.

## Inference & citation

- `by L` / `since L` (argument-free): cite lemma `L`; its explicit
  arguments are inferred from the goal and premises discharged from
  context. Use this instead of applying `L` to positional arguments.
- `?` — a hole in a function-call argument position, solved by unification
  from the goal/other arguments (does not invoke the auto-prover).
- `recalling f, g` after a `by`/`since` hint — bring extra named facts into
  the discharge scope.
- A context hypothesis `A ∧ B` makes both `A` and `B` available as facts
  (conjunction-elimination, recursive) — no manual `And.left`/`And.right`.
- `{x : T}` — an implicit parameter, solved by unification at call sites.
