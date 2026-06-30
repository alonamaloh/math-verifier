# Blueprint: Formalizing the Conway–Schneeberger / Bhargava Fifteen Theorem

> **Target.** A positive-definite quadratic form with an integer coefficient matrix
> is *universal* (represents every positive integer) **iff** it represents each of
> the nine critical numbers **{1, 2, 3, 5, 6, 7, 10, 14, 15}** — equivalently, iff it
> represents every integer from 1 to 15.
>
> Proof route: Bhargava's *escalator* method. Escalation from the zero lattice
> terminates at rank 4; the whole difficulty is proving each rank-4 escalator
> universal, which rests on the representation theory of the ternary sections.

**Primary source.** M. Bhargava, *On the Conway–Schneeberger fifteen theorem*,
Contemporary Mathematics **272** (2000), 27–37.
Hosted PDF: <http://www.fen.bilkent.edu.tr/~franz/mat/15.pdf>


## How to use this sheet

- Each item has an **ID** (e.g. `S0.D2`), a **status box**, an **effort tag**, and an
  **owes** field listing the IDs it depends on. Work bottom-up along the `owes` graph.
- **Status:** `[ ]` TODO · `[~]` WIP · `[B]` BLOCKED (note the blocker) · `[x]` DONE.
- **Effort:** `S` ≈ ≤2 days · `M` ≈ ~1 week · `L` ≈ 2–4 weeks · `XL` ≈ 1 month+.
- **★** marks the load-bearing theorems — the ones the rest of the stage leans on.
- "Library: …" notes which *existing* pieces of `library/` a stage builds on.

**Stage roll-up (skilled person-time; AI assistance compresses wall-clock more than the hard-reasoning stages):**

| Stage | Theme | Effort | Dominant risk |
|------|-------|--------|---------------|
| 0 | Linear algebra over ℤ/ℚ | ~4–6 wk | determinant + permutation sign from scratch |
| 1 | Quadratic forms & lattices | ~2–4 wk | isometry-invariance plumbing |
| 2 | Reduction & finiteness | ~3–6 wk | dedup-up-to-isometry to get exact counts |
| 3 | Escalation machinery | ~4–8 wk | machine-generating + deduping the ~207 rank-4 list |
| 4·P | p-adic foundations: re-introduce ℚ_p + carve ℤ_p toolkit | ~3–5 wk | dyadic (p=2) square classes |
| 4·L | local form theory: Hilbert symbol, Hasse invariant | ~3–5 wk | local representation bookkeeping |
| 4·G | genus / ℤ_p-lattices + three-squares (**gated**) | ~2–4 mo | dyadic Jordan theory; pay only if regularity is forced |
| 5 | Assembly & finite computation | ~3–8 wk | in-kernel performance of bounded checks |

*Stage 4 splits: **4·P** and **4·L** you build regardless (cheap, reusable); **4·G** is route-dependent — see the fork at the head of Stage 4 and defer it until `S3.E5` is in hand.*

**Conditional milestone (≈⅓ cost):** complete Stages 0–3 and 5 with every `S4.*`
admitted as an explicit axiom. That yields a kernel-checked *"Fifteen Theorem,
conditional on this finite table of ternary representation facts,"* and isolates
exactly which deep lemmas remain. Strongly recommended as the first publishable target.

---

## Stage 0 — Linear algebra over ℤ and ℚ

*Goal: vectors, matrices, the determinant, and the Gram machinery the form theory needs.*
*Library: `Algebra/` (IsRing/IsCommutativeRing/IsField), `Integer/`, `Rational/`, `Lists/` (permutations exist here), `Real/` for the ℝ-coefficient lemmas.*

**Vectors & matrices**
- `S0.V1` `[ ]` (S) Coordinate space `Vec R n` (`Fin n → R` or fixed-length list); module laws over a commutative ring. — owes: —
- `S0.V2` `[ ]` (S) Bilinear pairing `⟨·,·⟩ : Vec R n → Vec R n → R`; bilinearity, symmetry. — owes: S0.V1
- `S0.M1` `[ ]` (S) Matrices `Mat R m n`; matrix–vector and matrix–matrix product. — owes: S0.V1
- `S0.M2` `[ ]` (M) Product associativity & distributivity; identity matrix `I`; `I·A = A`. — owes: S0.M1
- `S0.M3` `[ ]` (S) Transpose; `(AB)ᵀ = BᵀAᵀ`, `(Aᵀ)ᵀ = A`. — owes: S0.M1

**Permutations & sign (prerequisite for the Leibniz determinant)**
- `S0.P1` `[ ]` (M) ★ Permutations of `Fin n`: group structure (compose, inverse, id). — owes: — · *Library: reuse `Lists/` permutation scaffolding if it generalizes; otherwise build on `Fin`.*
- `S0.P2` `[ ]` (L) ★ Sign of a permutation; well-defined parity; `sign` is a homomorphism (`sign(στ) = sign σ · sign τ`). — owes: S0.P1

**Determinant**
- `S0.D1` `[ ]` (M) Determinant via the Leibniz sum `det A = Σ_σ sign(σ) ∏ᵢ A[i,σi]`. — owes: S0.M1, S0.P2
- `S0.D2` `[ ]` (S) `det I = 1`; `det Aᵀ = det A`. — owes: S0.D1, S0.M3
- `S0.D3` `[ ]` (M) Multilinear & alternating in rows/columns; row swap flips sign; repeated row ⇒ `det = 0`. — owes: S0.D1
- `S0.D4` `[ ]` (L) ★ Multiplicativity: `det(AB) = det A · det B`. — owes: S0.D1, S0.D3
- `S0.D5` `[ ]` (M) Cofactor (Laplace) expansion along a row/column. — owes: S0.D1
- `S0.D6` `[ ]` (M) Adjugate; `A·adj(A) = det(A)·I`; over a field `A` invertible ⇔ `det A ≠ 0`; Cramer's rule. — owes: S0.D4, S0.D5
- `S0.D7` `[ ]` (M) Unimodular group `GLₙ(ℤ)`: integer `U` invertible over ℤ ⇔ `det U = ±1`. — owes: S0.D4, S0.D6

**Gram machinery (the bridge to forms)**
- `S0.G1` `[ ]` (S) Gram matrix `G = MᵀM` is symmetric; `xᵀGx = ‖Mx‖²`. — owes: S0.M3
- `S0.G2` `[ ]` (M) Cauchy–Binet `det(MᵀM) = Σ (k×k minors)²`; hence `det G ≥ 0` over ℝ. — owes: S0.D4, S0.D5
- `S0.G3` `[ ]` (M) Hadamard's inequality `det A ≤ ∏ ‖row_i‖` (for the reduction bounds in Stage 2). — owes: S0.G1

---

## Stage 1 — Quadratic forms and lattices

*Goal: the objects of the theorem and the monotonicity tool the closing argument uses.*
*Library: builds entirely on Stage 0; `Integer/`, `Rational/`, `Real/`.*

- `S1.F1` `[ ]` (S) Integer-matrix symmetric form: symmetric `A ∈ Mat ℤ n n`, `Q_A(x) = xᵀAx`. Fix the integer-matrix convention. — owes: S0.M1, S0.V2
- `S1.F2` `[ ]` (M) ★ Positive-definiteness `∀ x ≠ 0, Q(x) > 0` (over ℚ/ℝ coefficients of `x`). — owes: S1.F1
- `S1.F3` `[ ]` (M) Sylvester's criterion: all leading principal minors `> 0` ⇔ positive-definite. — owes: S1.F2, S0.D5
- `S1.R1` `[ ]` (S) `Represents Q n := ∃ x ∈ ℤⁿ, Q x = n`; `Universal Q := ∀ n > 0, Represents Q n`. — owes: S1.F1
- `S1.I1` `[ ]` (M) Isometry `A ≅ B := ∃ U ∈ GLₙ(ℤ), B = UᵀAU`; equivalence relation. — owes: S0.D7
- `S1.I2` `[ ]` (M) ★ Represented-set is an isometry invariant. — owes: S1.I1, S1.R1
- `S1.I3` `[ ]` (S) `disc Q := det A` is an isometry invariant (changes by `(det U)² = 1`). — owes: S0.D4, S1.I1
- `S1.S1` `[ ]` (M) ★★ **Sublattice monotonicity:** if a sublattice's form represents `n`, so does the whole form. *(The lever for every rank-4 universality proof.)* — owes: S1.R1
- `S1.S2` `[ ]` (S) Direct sum `Q ⊕ Q'`; `Represents (Q⊕Q') n` from representations of the summands. — owes: S1.R1
- `S1.B1` `[ ]` (S) Rank-1 form `x²` represents exactly the perfect squares; its truant is `2`. — owes: S1.R1
- `S1.B2` `[ ]` (M) ★ Positive-definiteness bound: for a reduced 2×2 section, `(2a_ij)² ≤ 4·a_ii·a_jj` (Cauchy–Schwarz on the form). *(Makes each escalation step finite.)* — owes: S1.F2

---

## Stage 2 — Reduction theory and finiteness

*Goal: turn "the escalator tree" into an explicit, finite, deduplicated object.*
*Library: Stage 0–1; `Real/` ordering and suprema.*

- `S2.R1` `[ ]` (L) Minkowski/Hermite reduction: every positive-definite form is isometric to a reduced one. — owes: S1.I1, S1.F2
- `S2.R2` `[ ]` (M) Hermite's inequality: `min Q ≤ c_n · (det A)^{1/n}`; bounds diagonal entries during escalation. — owes: S2.R1, S0.G3
- `S2.R3` `[ ]` (L) ★ Finiteness: only finitely many reduced positive-definite integer forms of each bounded rank and determinant; constructive enumeration. — owes: S2.R1, S1.B2
- `S2.R4` `[ ]` (L) ★ Decidable isometry on the bounded set, via a canonical reduced representative. *(Required to collapse the tree to the exact count, not merely a finite cover.)* — owes: S2.R3, S1.I1

---

## Stage 3 — Escalation machinery

*Goal: define escalation, generate the tree, and reduce universality to the nine numbers.*
*Library: Stage 0–2; `Lists/` for the enumerated trees; `Natural/` order for the truant.*

- `S3.T1` `[ ]` (M) ★ **Decidable bounded representation:** `Represents Q n` is decidable for `n ≤ N` — positive-definiteness confines the search `Q(x) = n` to a finite box `‖x‖ ≤ √(n / λ_min)`. — owes: S1.F2, S1.R1
- `S3.T2` `[ ]` (S) Truant `truant Q :=` least `t > 0` with `¬ Represents Q t`, well-defined for non-universal `Q`. — owes: S3.T1
- `S3.E1` `[ ]` (M) ★ Escalation step: the rank-(k+1) forms restricting to `Q` and representing `truant Q` in the new coordinate form a **finite, explicitly bounded** set. — owes: S3.T2, S1.B2, S2.R3
- `S3.E2` `[ ]` (S) Escalator lattice = iterated escalation from the rank-0 form; the escalator tree. — owes: S3.E1
- `S3.E3` `[ ]` (S) The **two** rank-2 escalators (explicit; from `x²` with truant 2 and the C–S bound). — owes: S3.E1, S1.B1
- `S3.E4` `[ ]` (M) The rank-3 escalators (explicit deduplicated list). — owes: S3.E2, S2.R4
- `S3.E5` `[ ]` (XL) ★★ The rank-4 escalators: machine-generate and dedup to the **≈207** isometry classes. *(Large mechanical lemma; the count is the checkpoint.)* — owes: S3.E2, S2.R4
- `S3.C1` `[ ]` (M) ★ The set of truants occurring anywhere in the tree is exactly **{1,2,3,5,6,7,10,14,15}**. — owes: S3.E3, S3.E4, S3.E5
- `S3.C2` `[ ]` (L) ★★ **Master reduction:** if `Q` represents the nine critical numbers then `Q` is universal — via: a non-universal `Q` would embed an escalator missing its truant ∈ {nine}. *(Depends on rank-4 universality, Stage 5.)* — owes: S3.C1, S3.E5, S5.U2

---

## Stage 4 — Ternary representation theory (deep core)

*Goal: for each ternary section used in Stage 5, prove exactly which integers it represents.*
*Library note: **p-adics are not currently in `library/`** (removed) — block **4·P** re-introduces them. The existing feeders are `IntegerMod/` (ℤ/pᵏ, and F_p at a prime), `FiniteField/`, `Polynomial/`, and `Rational/`.*

> **The fork that decides this stage's size.** Hasse–Minkowski gives representation
> over **ℚ** (`∃ x ∈ ℚⁿ`); the theorem needs representation over **ℤ** (`∃ x ∈ ℤⁿ`).
> Closing that gap is genus theory, whose local objects are **ℤ_p-lattices**, not
> ℚ_p-forms. Hence the three blocks below are *not* equally committed:
> - **4·P** and **4·L** (ℤ_p as a *ring*; Hilbert symbol; Hasse invariant) you need
>   **regardless** — cheap relative to ℚ_p itself, and reusable well beyond this project.
> - **4·G** (ℤ_p-*lattices*, Jordan splitting, genus/regularity) is **gated** — its
>   weight is real, so pay it only for the ternaries that genuinely force it.
>   **Defer the commit until `S3.E5` has enumerated the actual sections.**
> - **Escape hatch:** for many small ternaries the local conditions are plain
>   congruences (`n ≢ 7 mod 8`, …), provable **directly in `IntegerMod/`** with no
>   lattice apparatus. For ~20–30 named forms, finite ℤ/pᵏ arguments are often the
>   lighter path and keep p-adics confined to the single clean Hasse–Minkowski statement.

**Block 4·P — p-adic foundations (do-now; reusable)**
- `S4.P1` `[ ]` (M) Re-introduce **ℚ_p** as the p-adic-Cauchy completion of ℚ, parallel to `Real/`: field structure, p-adic absolute value, embedding ℚ ↪ ℚ_p. — owes: `Rational/` · *Mirror the `Real/` Cauchy-quotient pattern — expose a clean interface and never touch the quotient downstream.*
- `S4.P2` `[ ]` (S) ★ **ℤ_p as the valuation subring** `{x : |x|_p ≤ 1}` — a definable subring, not a second completion. Valuation `v_p`; factorization `x = p^{v(x)}·u`. — owes: S4.P1
- `S4.P3` `[ ]` (S) Unit group `ℤ_p^* = {|x|_p = 1}`; residue map `ℤ_p ↠ ℤ_p/pℤ_p ≅ F_p`. — owes: S4.P2 · *Library: identify the residue field with `IntegerMod/` at a prime / `FiniteField/`.*
- `S4.P4` `[ ]` (M) ★ **Hensel's lemma** (simple-root lift). — owes: S4.P3
- `S4.P5` `[ ]` (M) ★★ **Square classes** `ℚ_p^*/(ℚ_p^*)²`: order 4 for odd p, **order 8 for p = 2**; test squareness of a unit via Hensel (mod p for odd p, **mod 8 for p = 2**). *(The dyadic case is the cost center of the local layer — budget for it explicitly.)* — owes: S4.P4

**Block 4·L — local form theory**
- `S4.L1` `[ ]` (L) **Hilbert symbol** `(a,b)_p` and its bilinearity / explicit formulas. — owes: S4.P5
- `S4.L2` `[ ]` (L) **Hasse invariant** of a form over ℚ_p; isometry classification of p-adic forms (rank, disc, Hasse). — owes: S4.L1
- `S4.L3` `[ ]` (M) Local representation criterion over ℚ_p and ℝ (`p = ∞`): when a local form represents a given local number. — owes: S4.L2

**Block 4·G — genus / ℤ_p-lattices (gated; defer until `S3.E5`)**
- `S4.G0` `[ ]` (L) ★ **ℤ_p-lattice theory**: lattices over ℤ_p, GLₙ(ℤ_p)-isometry, **Jordan splitting** (including the dyadic `p = 2` theory). *(The real weight of 4·G; skip entirely if the escape hatch covers every section.)* — owes: S4.P3
- `S4.G1` `[ ]` (XL) ★★ **Hasse–Minkowski** (local-global) for rational representation — or a restricted version sufficient for the ternaries that occur. — owes: S4.L3
- `S4.G2` `[ ]` (L) Genus & regularity: one class per genus ⇒ local *integral* representability is global. — owes: S4.G1, S4.G0, S2.R4
- `S4.N1` `[ ]` (XL) ★★ **Three-squares theorem**: `n = x²+y²+z²` ⇔ `n ≠ 4^a(8b+7)`. Slick route = regularity of `x²+y²+z²` (uses `S4.G0/G2`); alternatives (Dirichlet-on-AP, or a Minkowski geometry-of-numbers argument) sidestep p-adics but trade in other heavy machinery. — owes: S4.G2 *(regularity route)* **or** external
- `S4.S*` `[ ]` (M each) ★ For each ternary section `T_i` from `S3.E5` (`x²+y²+2z²`, `x²+2y²+2z²`, `x²+y²+3z²`, …): its exact represented-set, via **(a)** `IntegerMod/` congruences (escape hatch), **(b)** `S4.G2` regularity, or **(c)** direct argument. *(Tag each section with the route it actually needed.)* — owes: S4.L3, plus per-section S4.G2 / `IntegerMod/`
- `S4.Q1` `[ ]` (L) *(Alternative tail route)* Tartakowsky-type bound: a positive quaternary represents all **sufficiently large** integers meeting the local conditions — reduces each rank-4 universality to a finite check. — owes: S4.L3

---

## Stage 5 — Assembly and the finite computations

*Goal: per-escalator universality and the final theorem.*
*Library: Stage 0–4; relies on the kernel's computation/reflection for the bounded checks.*

- `S5.K1` `[ ]` (L) ★ Make `S3.T1`'s bounded representation check **compute efficiently in-kernel** to the bounds needed (the "rather large calculation"). *(Performance risk — prototype before committing; verify the kernel can discharge a few thousand bounded checks.)* — owes: S3.T1
- `S5.U1` `[ ]` (M) ★ Universality template: given a rank-4 escalator `L`, a ternary section `L3 ⊆ L` with known represented-set (Stage 4), and the 4th coordinate covering the residual exceptions ⇒ `L` universal. — owes: S1.S1, S4.S*, S5.K1
- `S5.U2` `[ ]` (XL) ★★ Apply `S5.U1` across all **≈207** rank-4 escalators (mostly schematic over a shared lemma; a handful need bespoke handling). — owes: S5.U1, S3.E5
- `S5.U3` `[ ]` (M) Handle the few escalations that only resolve at **rank 5**. — owes: S5.U1, S3.E5
- `S5.F1` `[ ]` (M) ★★ **Fifteen Theorem:** combine `S3.C2` + `S5.U2` + `S5.U3`. State both forms: "represents the nine criticals ⇒ universal" and "represents 1…15 ⇒ universal." — owes: S3.C2, S5.U2, S5.U3
- `S5.F2` `[ ]` (S) *(Optional)* Minimality: {1,2,3,5,6,7,10,14,15} is the unique minimal forcing set. — owes: S5.F1, S3.C1

---

## Critical path & forks

```
S0.P2 ─► S0.D1 ─► S0.D4 ─┬─► S0.D7 ─► S1.I1 ─► S1.I2/S1.S1
                         └─► S0.G2 (Gram, → S4.N1 alt route)
S1.B2 ─► S2.R3 ─► S2.R4 ─► S3.E5 ──────────────────────────┐
S1.F2 ─► S3.T1 ─► S3.E1 ─► S3.C1 ─► S3.C2 ◄─┐              │
                                            │              ▼
S4.P1 ─► S4.P5 ─► S4.L3 ─┬─► S4.G1 ─► S4.G2 ─► S4.S* ─► S5.U1 ─► S5.U2 ─► S5.F1
        (do-now / 4·P,L) └─ gated 4·G ────┘   ▲                ▲
                          IntegerMod/ ────────┘ (escape hatch) S5.K1 ─┘
```

- **Shared trunk:** `S0.D*` (determinant) feeds *both* the form/isometry side and the
  Gram side — the reason Stage 0 is worth building well.
- **Two independent long poles** that can progress in parallel: the *combinatorial*
  pole (`S2 → S3.E5`, large but elementary) and the *arithmetic* pole (`S4`, deep).
  They only meet at `S5.U1`.
- **Inside the arithmetic pole, a second split:** `4·P`/`4·L` (re-introduce ℚ_p, carve
  ℤ_p, Hilbert/Hasse) are **do-now and reusable**; only the gated `4·G`
  (ℤ_p-lattices/genus) is route-dependent. The `IntegerMod/` escape hatch can satisfy
  `S4.S*` for many sections without touching `4·G` at all.
- **Earliest honest deliverable:** `S5.F1` with all `S4.*` axiomatized — finishable
  once Stages 0–3 + `S5.K1`/`S5.U1` schema are done, before the arithmetic pole lands.
  (Building `4·P`/`4·L` anyway is cheap and de-risks the eventual de-axiomatization.)
- **Prototype early & sequence the gate:** `S5.K1` (kernel computation) and `S3.E5`
  (the dedup/count) first — if either is intractable, it reshapes the whole plan.
  Then enumerate the `S4.S*` sections out of `S3.E5` and **tag each by route**
  (`IntegerMod/` congruence vs. forced regularity) *before* committing to `4·G`.

