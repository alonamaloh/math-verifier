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

> **Gap assessment 2026-07-18:** the linear-algebra build (PLAN_LINEAR_ALGEBRA,
> rank–nullity + det(AB)) and the Cayley–Hamilton arc (PLAN_CAYLEY_HAMILTON,
> C1–C6) landed most of Stage 0 since this sheet was written — determinant,
> permutation sign, multiplicativity, Laplace expansion, and the adjugate all
> exist over an abstract `CommutativeRing`. **Stage 0's dominant risk
> ("determinant + permutation sign from scratch") is retired.** Remaining
> Stage 0 gaps: transpose (S0.M3, and with it det Aᵀ), the unimodular group
> (S0.D7), the Gram block (S0.G1–G3, not needed before Stage 2), the abstract
> bilinear pairing (S0.V2), and the field-invertibility/Cramer half of S0.D6.
> Stage 1 is untouched but its Stage-0 inputs are now nearly all on the shelf.
> Item-level status boxes below updated with file pointers.

> **Route note 2026-07-18 (owner-endorsed).** The stage numbers are
> thematic, NOT topological: the Stage-3 spine `S3.T1 → T2 → E1 → E3`
> owes only `S1.F2 + S1.R1` (+ `S1.B2` for E1's finiteness) — nothing in
> Stage 2. Stage 2 enters only where exact counts up to isometry are
> needed (`S2.R4` feeding E4/E5). Execution order therefore:
> **(1)** finish Stage 1 with B1/B2 as first-class (the pulled-forward
> spine consumes them); **(2)** the `S5.K1` compute spike IMMEDIATELY
> after (see the note at S5.K1); **(3)** the Stage-3 spine T1/T2/E1/E3,
> with E1 tried on B2-only bounds (note at S3.E1); **(4)** Stage 2 scoped
> by what (3) revealed, led by R4 with the dedup machinery shaped by
> E4's live candidate list — R1/R2 only as forced; **(5)** E4 → E5 (the
> ≈207 checkpoint) closed with a route-tagging pass over the ternary
> sections (congruence-only / Davenport–Cassels / genuinely-needs-genus);
> **(6)** the conditional milestone (C1, U1, U2-with-axioms, U3, C2,
> conditional F1) — waits on nothing in the arithmetic pole;
> **(7)** the ℚ_p pole interleaved rather than queued, with
> Davenport–Cassels proved EARLY (elementary descent; upgrades the
> escape hatch for every Euclidean ternary) and 4·G strictly behind
> (5)'s route tags. Front-loaded so the two risks velocity data cannot
> predict — in-kernel compute and dedup at scale — are the next two
> things learned.

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
- `S0.V1` `[x]` (S) Coordinate space `Vec R n` (`Fin n → R` or fixed-length list); module laws over a commutative ring. — owes: — · **DONE:** `Algebra/coordinate_space.math` (`CoordinateSpace` + `vector_space`); plus span/dimension/subspace/rank–nullity beyond this sheet's ask.
- `S0.V2` `[x]` (S) Bilinear pairing `⟨·,·⟩ : Vec R n → Vec R n → R`; bilinearity, symmetry. — owes: S0.V1 · **DONE 2026-07-18:** `Algebra/matrix_vector.math` — ring-level `RingVector(r, n)` (the field-based `CoordinateSpace` stays with the vector-space layer), `innerProduct` with symmetry/additivity/homogeneity, the matrix action `A · x` with identity/compose laws, and the adjoint law `⟨Aᵀ·u, v⟩ = ⟨u, A·v⟩` (the Gram bridge).
- `S0.M1` `[x]` (S) Matrices `Mat R m n`; matrix–vector and matrix–matrix product. — owes: S0.V1 · **DONE:** `Algebra/matrix.math` (`Matrix(c, m, n)`, multiply/add/scale/identity; matrix–vector product still implicit via 1-column).
- `S0.M2` `[x]` (M) Product associativity & distributivity; identity matrix `I`; `I·A = A`. — owes: S0.M1 · **DONE:** `Algebra/matrix_ring.math` + the `Matrix.ring` bundle (Cayley–Hamilton C5).
- `S0.M3` `[x]` (S) Transpose; `(AB)ᵀ = BᵀAᵀ`, `(Aᵀ)ᵀ = A`. — owes: S0.M1 · **DONE 2026-07-18:** `Algebra/matrix_transpose.math` — postfix `ᵀ` (new lexer token, wired like `⁻¹`; postfix results accept call arguments, so `Aᵀ(j, i)` reads naturally), `transpose_entry`, `transpose_transpose`, `transpose_add`/`_scale`, `Iᵀ = I`, `(A·B)ᵀ = Bᵀ·Aᵀ`.

**Permutations & sign (prerequisite for the Leibniz determinant)**
- `S0.P1` `[x]` (M) ★ Permutations of `Fin n`: group structure (compose, inverse, id). — owes: — · **DONE:** `Algebra/finite_permutation.math` (compose/inverse/identity + laws, swaps, extend).
- `S0.P2` `[x]` (L) ★ Sign of a permutation; well-defined parity; `sign` is a homomorphism (`sign(στ) = sign σ · sign τ`). — owes: S0.P1 · **DONE:** `Algebra/permutation_sign.math` (`Permutation.sign_compose`, `sign_is_unit`) + `permutation_transposition_sign.math` (`sign_swap`).

**Determinant**
- `S0.D1` `[x]` (M) Determinant via the Leibniz sum `det A = Σ_σ sign(σ) ∏ᵢ A[i,σi]`. — owes: S0.M1, S0.P2 · **DONE:** `Algebra/determinant.math` (`Matrix.determinant`, `determinant_expansion`), over an abstract `CommutativeRing`.
- `S0.D2` `[x]` (S) `det I = 1`; `det Aᵀ = det A`. — owes: S0.D1, S0.M3 · **DONE 2026-07-18.** `Algebra/determinant_transpose.math` (entry-product reindex along σ + `sign_inverse` + summing over the inversion rearrangement; new general lemmas `Permutation.inverse_inverse`, `Permutation.sign_inverse`, `inverse_map_permutes_allPermutations`) and `Algebra/determinant_identity.math` (`det I = 1` by delta-collapse to the identity term; new aggregation lemmas `productOver_one_function`, `productOver_zero_on_member`; general `Permutation.moved_index_of_not_identity`).
- `S0.D3` `[x]` (M) Multilinear & alternating in rows/columns; row swap flips sign; repeated row ⇒ `det = 0`. — owes: S0.D1 · **DONE (rows):** `Algebra/determinant_row_permutation.math` + `alternating_collapse.math` + `adjugate.math` (`determinant_updateRow_*`, repeated row). Column versions follow from `det Aᵀ` once S0.M3 lands.
- `S0.D4` `[x]` (L) ★ Multiplicativity: `det(AB) = det A · det B`. — owes: S0.D1, S0.D3 · **DONE:** `Algebra/determinant_multiplicative.math` (`Matrix.determinant_multiply`).
- `S0.D5` `[x]` (M) Cofactor (Laplace) expansion along a row/column. — owes: S0.D1 · **DONE (rows):** `Algebra/adjugate.math` (`Matrix.determinant_row_expansion`, landed with the Cayley–Hamilton arc).
- `S0.D6` `[~]` (M) Adjugate; `A·adj(A) = det(A)·I`; over a field `A` invertible ⇔ `det A ≠ 0`; Cramer's rule. — owes: S0.D4, S0.D5 · **Adjugate + `multiply_adjugate` DONE** (`Algebra/adjugate.math`); **field invertibility ⇔ `det ≠ 0` DONE 2026-07-18** (`Algebra/matrix_field_inverse.math`, both directions over `Field.commutative_ring`). **Cramer DEFERRED**: no downstream consumer in this arc's graph yet, and its natural proof wants the column-update dual of the `updateRow` machinery — build it alongside Sylvester (S1.F3), which forces submatrix/minor tooling anyway.
- `S0.D7` `[x]` (M) Unimodular group `GLₙ(ℤ)`: integer `U` invertible over ℤ ⇔ `det U = ±1`. — owes: S0.D4, S0.D6 · **DONE 2026-07-18:** `Algebra/matrix_inverse.math` (two-sided `Matrix.IsInvertible`, adjugate right inverse, `invertible_of_unit_determinant` with the U = U·(V·W) = W bootstrap, `determinant_unit_of_right_inverse`) + `Algebra/unimodular.math` (both directions over `Integer.commutative_ring_bundle`) + `Integer/units.math` (`Integer.multiply_one_implies_unit`: the units of ℤ are ±1, via |x|·|y| = 1 at ℕ). New matrix-ring laws: `scale_scale`, `one_scale`.

**Gram machinery (the bridge to forms)**
- `S0.G1` `[x]` (S) Gram matrix `G = MᵀM` is symmetric; `xᵀGx = ‖Mx‖²`. — owes: S0.M3 · **DONE 2026-07-18:** `Algebra/gram.math` — symmetry via `transpose_multiply` + involution; `⟨x, G·x⟩ = ⟨M·x, M·x⟩` via `applyVector_multiply` + the adjoint law.
- `S0.G2` `[ ]` (M) Cauchy–Binet `det(MᵀM) = Σ (k×k minors)²`; hence `det G ≥ 0` over ℝ. — owes: S0.D4, S0.D5 · **DEFERRED to Stage 2 kickoff** (consumer-first: the minor machinery should be shaped by S2.R2/Sylvester's needs; same call as Cramer).
- `S0.G3` `[ ]` (M) Hadamard's inequality `det A ≤ ∏ ‖row_i‖` (for the reduction bounds in Stage 2). — owes: S0.G1 · **DEFERRED to Stage 2 kickoff** (needs ℝ norms; its only consumer is S2.R2).

---

## Stage 1 — Quadratic forms and lattices

*Goal: the objects of the theorem and the monotonicity tool the closing argument uses.*
*Library: builds entirely on Stage 0; `Integer/`, `Rational/`, `Real/`.*

- `S1.F1` `[x]` (S) Integer-matrix symmetric form: symmetric `A ∈ Mat ℤ n n`, `Q_A(x) = xᵀAx`. Fix the integer-matrix convention. — owes: S0.M1, S0.V2 · **DONE 2026-07-18:** `Algebra/quadratic_form.math` — `Matrix.IsSymmetric`, `Matrix.quadraticForm(A, x) = ⟨x, A·x⟩` over an abstract `CommutativeRing` (integer-matrix convention documented in the header), plus the load-bearing pullback law `Q_{MᵀAM}(x) = Q_A(M·x)` for **rectangular** M (one lemma serves isometry AND sublattice restriction) and symmetry preservation under pullback.
- `S1.F2` `[x]` (M) ★ Positive-definiteness `∀ x ≠ 0, Q(x) > 0`. — owes: S1.F1 · **Definition landed 2026-07-18** (`Algebra/integer_quadratic_form.math`, `Matrix.IsPositiveDefinite`); **OWNER DECISION (2026-07-18, pre-Sylvester consolidation T5.2): the ℤ-vector statement is CONFIRMED as the primitive.** ℚ agreement = denominator-clearing via `quadraticForm_scale` (landed). The ℝ statement is a Sylvester corollary at its first consumer (S2.R2 / S3.T1) — do NOT attempt via density: positivity on a dense set yields only semi-definiteness in the limit; the gap needs rational-kernel-of-PSD or the Sylvester route. Isometry-invariance of positive-definiteness: `Matrix.isometric_positive_definite`, landed with the T5.1 riders.
- `S1.F3` `[x]` (M) Sylvester's criterion: all leading principal minors `> 0` ⇔ positive-definite. — owes: S1.F2, S0.D5 · **COMPLETE 2026-07-18** (`Algebra/schur_complement.math` + `Algebra/sylvester.math`, both manifest-added at zero leaks, budget 394 held): bordered vocabulary (`leadingBlock`/`borderColumn`/`corner`, `RingVector.restrict`/`extend` with extension = inclusion-matrix action), `bordered_decomposition`, `quadraticForm_bordered` splitting, `schurComplement` (s = det(A')·c − ⟨adj(A')·b, b⟩), identity (i) `quadraticForm_schurComplement`, identity (ii) `determinant_schurComplement` via the border-elimination matrix **G = [[I, −adj(A')·b],[0, det A']]** (SIMPLER than the plan's E: B·G = [[A', 0],[bᵀ, s]], so `det(c•I) = cᵐ` and det(adj) are NOT needed — the planned E-route arithmetic didn't close), `determinant_bordered_top_column` (transpose pass-through), and both Sylvester directions by induction in `Matrix.determinant_positive_of_positive_definite` / `positive_leading_minors_of_positive_definite` / `positive_definite_of_positive_leading_minors` (`HasPositiveLeadingMinors`; ℤ positivity suite added to Integer/order.math + integral_domain.math). Frictions: QUIRK Q9 (under-binder congruence falls through on compound-head slots), scale-operator dispatch needs carrier-typed lets, ring-at-bundle doesn't identify `Integer.zero` with `CommutativeRing.zero(bundle)`. **Foundation (earlier 2026-07-18)** (commits 64f94acd..c5a9f4b2): `Algebra/matrix_submatrix.math` (`Matrix.submatrix` reindexing, `leadingSubmatrix` via `NaturalsBelow.embed`, `inclusionMatrix` + submatrix-as-pullback, injective selections preserve nonzero), PD-inheritance (`positive_definite_section`/`_leadingSubmatrix`/`_diagonal`, `quadraticForm_submatrix`/`_standardBasis`), **`Permutation.sign_extend`** (the size-crossing sign bridge; new `Algebra/permutation_sign_extend.math` + `List.filter_append`/`filter_none`/`filter_map`), and **`Matrix.determinant_bordered_top_row`** (`Algebra/determinant_bordered.math`: concentrated top row ⇒ det M = det(block)·corner; also `NaturalsBelow.inclusion_or_top`). **Chosen route is FRACTION-FREE over ℤ — no ℚ needed**: with B = [[A', b],[bᵀ, c]] symmetric and s := det(A')·c − ⟨adj(A')·b, b⟩, prove (i) `(det A')²·Q_B(x) = Q_{A'}(det(A')·y + t·adj(A')·b) + t²·det(A')·s` (pure bilinear algebra via the adjugate identity; needs `applyVector_add`, `innerProduct` right-side laws, Q-of-sum expansion) and (ii) `det B · (det A')ᵐ⁺¹-free form`: det(A')·det(B) = det(A')·s via B·E = [[det A'·I, 0],[bᵀadjA', s]] with E = [[adj A', −adj(A')·b],[0, det A']] (needs det(c•I) = cᵐ, bordered column version via `determinant_transpose`, and integral-domain cancellation — acceptable: consumers have det A' > 0). Both directions of Sylvester then follow by induction using the bordered decomposition (REMAINING WORK). Frictions filed as QUIRK Q6–Q8.
- `S1.R1` `[x]` (S) `Represents Q n := ∃ x ∈ ℤⁿ, Q x = n`; `Universal Q := ∀ n > 0, Represents Q n`. — owes: S1.F1 · **DONE 2026-07-18:** `Matrix.Represents(A, target : ℤ)` and `Matrix.IsUniversal` (∀ m ≥ 1) in `Algebra/integer_quadratic_form.math`.
- `S1.I1` `[x]` (M) Isometry `A ≅ B := ∃ U ∈ GLₙ(ℤ), B = UᵀAU`; equivalence relation. — owes: S0.D7 · **DONE 2026-07-18:** `Matrix.IsIsometric` (generic: invertible U over any commutative ring; over ℤ that is GLₙ(ℤ) by S0.D7) with `reflexive`/`symmetric`/`transitive`, plus `Matrix.identity_invertible` and `Matrix.invertible_multiply` in `Algebra/matrix_inverse.math`.
- `S1.I2` `[x]` (M) ★ Represented-set is an isometry invariant. — owes: S1.I1, S1.R1 · **DONE 2026-07-18:** `Matrix.isometric_represents` + `Matrix.isometric_universal` (converse direction via `IsIsometric.symmetric`).
- `S1.I3` `[x]` (S) `disc Q := det A` is an isometry invariant (changes by `(det U)² = 1`). — owes: S0.D4, S1.I1 · **DONE 2026-07-18:** `Matrix.determinant_pullback` (generic `det(UᵀAU) = (det U)²·det A`) + `Matrix.isometric_determinant` over ℤ (via `Integer.unit_squares_to_one`, new in `Integer/units.math`, now also cited by `unimodular.math`).
- `S1.S1` `[x]` (M) ★★ **Sublattice monotonicity:** if a sublattice's form represents `n`, so does the whole form. *(The lever for every rank-4 universality proof.)* — owes: S1.R1 · **DONE 2026-07-18:** `Matrix.represents_of_sublattice` — a representation of the pulled-back form `MᵀAM` (M rectangular = a finite-index or lower-rank sublattice) is a representation of `A` at `M·x`.
- `S1.S2` `[x]` (S) Direct sum `Q ⊕ Q'`; `Represents (Q⊕Q') n` from representations of the summands. — owes: S1.R1 · **DONE 2026-07-19** (`Algebra/matrix_direct_sum.math`, manifest-added at zero leaks): `Matrix.directSum := J_L·A·J_Lᵀ + J_R·B·J_Rᵀ` — assembled from the new **inclusion-matrix calculus** (4 generic placed-entry laws in `matrix_submatrix.math`), so NO index case-split in the definition; `sumLeft`/`shift` index embeddings (injective/disjoint/covering), four block-entry laws, `directSum_symmetric`, four block pullbacks (diagonal recover the summands, off-diagonal vanish), `directSum_quadraticForm` (Q additive on decomposed vectors), `restrictLeft/Right` + `directSum_decomposition`; ℤ layer in `integer_quadratic_form.math`: `directSum_represents_left/right` (via `represents_of_sublattice` — the escalation lever), `directSum_universal_left`, `directSum_positive_definite`.
- `S1.B1` `[x]` (S) Rank-1 form `x²` represents exactly the perfect squares; its truant is `2`. — owes: S1.R1 · **DONE 2026-07-19** (`Algebra/square_form.math`, manifest-added at zero leaks, budget 394 held): `Matrix.squareForm := Matrix.identity(Integer.commutative_ring_bundle, 1)`, `RingVector.coordinate` + `coordinate_decomposition` (every 1-dim vector is coordinate·e₀ — generic over the ring), `squareForm_value` (Q(x) = coordinate²) via `quadraticForm_scale` + `quadraticForm_standardBasis`, `squareForm_represents_square`/`_represents_only_squares` (the two directions of "values = perfect squares"), `squareForm_represents_one`, `squareForm_not_represents_two` via new `Integer.two_is_not_a_square` (sign-split to ℕ) + `Natural.two_is_not_a_square` (Natural/multiply_bounds.math; squares jump 1 → 4). The formal `truant(squareForm) = 2` equation lands with S3.T2's definition; these two lemmas are its content. NOTE: written the session the matcher/normalization fixes landed — the whole file verified on the FIRST kernel run (bundle zero/one identification, under-binder β-contraction, `• ` half-match dispatch all load-bearing).
- `S1.B2` `[x]` (M) ★ Positive-definiteness bound: for a reduced 2×2 section, `(2a_ij)² ≤ 4·a_ii·a_jj` (Cauchy–Schwarz on the form). *(Makes each escalation step finite.)* — owes: S1.F2 · **DONE 2026-07-19** (`Matrix.cauchy_schwarz_entry_bound`, `integer_quadratic_form.math`): the STRICT form `A(i,j)² < A(i,i)·A(j,j)` for symmetric PD and i ≠ j, by evaluating Q at `A(j,j)·e_i − A(i,j)·e_j` (value factors as `A(j,j)·(A(i,i)A(j,j) − A(i,j)²)`) — no determinant machinery; the sheet's 4-scaled ≤ form follows by weakening at the consumer. Riders: `RingVector.innerProduct_standardBasisRow_left`, `Integer.lt_of_positive_difference`.

---

## Stage 2 — Reduction theory and finiteness

*Goal: turn "the escalator tree" into an explicit, finite, deduplicated object.*
*Library: Stage 0–1; `Real/` ordering and suprema.*

> *Route note 2026-07-18: enter this stage AFTER the pulled-forward
> Stage-3 spine, LED BY R4 — decidable isometry with canonical
> representatives is what E4/E5 truly require, and its dedup machinery
> should be shaped against E4's live rank-3 candidate list. R1/R2 are
> the two L-effort items that may never be fully needed (see the S3.E1
> note); build them only to the extent the spine demanded.*

- `S2.R1` `[ ]` (L) Minkowski/Hermite reduction: every positive-definite form is isometric to a reduced one. — owes: S1.I1, S1.F2
- `S2.R2` `[ ]` (M) Hermite's inequality: `min Q ≤ c_n · (det A)^{1/n}`; bounds diagonal entries during escalation. — owes: S2.R1, S0.G3
- `S2.R3` `[ ]` (L) ★ Finiteness: only finitely many reduced positive-definite integer forms of each bounded rank and determinant; constructive enumeration. — owes: S2.R1, S1.B2
- `S2.R4` `[ ]` (L) ★ Decidable isometry on the bounded set, via a canonical reduced representative. *(Required to collapse the tree to the exact count, not merely a finite cover.)* — owes: S2.R3, S1.I1

---

## Stage 3 — Escalation machinery

*Goal: define escalation, generate the tree, and reduce universality to the nine numbers.*
*Library: Stage 0–2; `Lists/` for the enumerated trees; `Natural/` order for the truant.*

- `S3.T1` `[x]` (M) ★ **Decidable bounded representation:** `Represents Q n` is decidable for `n ≤ N` — positive-definiteness confines the search `Q(x) = n` to a finite box `‖x‖ ≤ √(n / λ_min)`. — owes: S1.F2, S1.R1 · **DONE 2026-07-19** (`Algebra/representation_bound.math`, manifest-added at zero leaks): the box-bound THEOREM route (per the K1 verdict — witness positives are ~3 ms, so only the negative side needs theory). Fraction-free over ℤ, no λ_min/ℝ: **`Matrix.positive_definite_box_bound`** `det(A)·x(i)² ≤ adj(A)(i,i)·Q(x)` via Cauchy–Schwarz for the A-pairing (`Matrix.cauchy_schwarz_vector_bound`, ⟨u,Av⟩² ≤ Q(u)Q(v), same eliminating-vector recipe as B2) evaluated at the integral vector adj(A)·e_i — whose A-pairing with x is det(A)·x(i) and whose own value is det(A)·adj(A)(i,i) (`quadraticForm_adjugate_column`; only the RIGHT adjugate identity + adjoint law + symmetry, no adjugate-transpose lemma). Consumer faces: `represents_within_box` (every representation of `target` lies in the explicit box) and `value_exceeds_outside_box` (outside it, Q > target — with `adjugate_diagonal_positive`). Riders: `Integer.cancel_le/lt_by_positive`, `Integer.positive_difference_of_lt`, `Matrix.quadraticForm_nonneg`.
- `S3.T2` `[x]` (S) Truant `truant Q :=` least `t > 0` with `¬ Represents Q t`, well-defined for non-universal `Q`. — owes: S3.T1 · **DONE 2026-07-19** (`Algebra/truant.math`, manifest-added at zero leaks): `Matrix.IsTruant` (least positive missed integer) + accessor lemmas (`positive`/`missed`/`represents_below`/`not_universal`); existence for non-universal forms via `Logic.not_forall_implies_exists_not` + `Natural.least_witness` (both need `predicate := …` named-argument — higher-order inference can't solve the predicate); uniqueness by trichotomy; **total function `Matrix.truant` by definite description** over the junk-total predicate (reciprocal_function pattern, junk 0 on universal forms; `Logic.the` arguments bound as named claims so the file is leak-free) with `truant_is_truant`/`truant_equals`. The formal root equation: **`Matrix.truant(Matrix.squareForm) = 2`** (+ `squareForm_not_universal`, `IsTruant(squareForm, 2)`).
- `S3.E1` `[x]` (M) ★ Escalation step: the rank-(k+1) forms restricting to `Q` and representing `truant Q` in the new coordinate form a **finite, explicitly bounded** set. — owes: S3.T2, S1.B2, ~~S2.R3~~ · **DONE 2026-07-19 on the B2-only route** (`Algebra/escalation.math`, manifest-added at zero leaks): `Matrix.IsEscalation(A, B)` = symmetric PD bordered extension (schur vocabulary: `leadingBlock(B) = A`, `corner(B) = (truant(A) : ℤ)` — total truant makes the definition hypothesis-free; universal forms have no escalations since corner 0 can't be PD). `escalation_represents_truant` (at the new basis vector), block inherits symmetry/PD, and ★ **`escalation_border_bound`**: `b_i² < A(i,i)·truant(A)` straight from `cauchy_schwarz_entry_bound` — the explicit finite cover, NO Minkowski. The canonical constructor **`Matrix.borderedAssembly(A,b,c) = [[A,b],[bᵀ,c]]`** now has block/border/corner/symmetry faces, and `Matrix.IsEscalation.eq_borderedAssembly` reconstructs every escalation from its border. Formal finite-list enumeration remains in the tree stages (E4/E5).
- `S3.E2` `[x]` (S) Escalator lattice = iterated escalation from the rank-0 form; the escalator tree. — owes: S3.E1 · **DONE 2026-07-19** (`Algebra/escalator_tree.math`, manifest-added; leak budget 394 → 397 for the three `unfold Natural.add` boundary markers of the rank recursion — the pattern-match arm plus the two quarantining faces, `enumerate`-class): **`Matrix.IsEscalator`** by recursion on rank (`| 0 => True | 1 + m => ∃ A. IsEscalator(m, A) ∧ IsEscalation(A, B)`), with faces `escalator_empty`/`escalator_step`/`escalator_split` so consumers never unfold the recursion. Rank-0 theory: the empty form represents exactly 0 (`zero_dimension_quadraticForm/_represents/_represents_zero`), is non-universal with **`truant = 1`**, and is vacuously symmetric/PD. Every escalator is symmetric + PD (`escalator_symmetric/_positive_definite`, induction with the last escalation's faces). ★ **`escalator_rank_one`**: the unique rank-1 escalator IS `squareForm` on the nose (corner = cast truant 1, 1×1 extensionality); **`escalator_rank_two`** splices E3 (isometric to x²+y² or x²+2y²). ★ **Escalation existence**: generic `Matrix.diagonalExtension(A, c) := J·A·Jᵀ + c•topUnit` (new `NaturalsBelow.topSelector` + `Matrix.topUnit`; leadingBlock/borderColumn(=0)/corner faces via the placed-entry calculus — the batch-3 wrapper-head fix carries the entry citations directly), symmetric + PD when A is and c > 0 (zero-border bordered splitting `Q_D(x) = Q_A(y) + t²·c`); `escalation_exists` (symmetric+PD+non-universal ⇒ ∃ escalation, corner = truant) and `escalator_escalation_exists` (the tree only terminates at universal forms).
- `S3.E3` `[x]` (S) The **two** rank-2 escalators (explicit; from `x²` with truant 2 and the C–S bound). — owes: S3.E1, S1.B1 · **DONE 2026-07-19** (`Algebra/rank_two_escalators.math`, manifest-added at zero leaks): ★ **`Matrix.rank_two_escalators`** — every escalation of x² is isometric to `sumOfTwoSquaresForm` (x²+y², now a library definition; = identity(2) via new generic `Matrix.directSum_identity`) or `squarePlusDoubleSquareForm` (x²+2y²). Route: border bound + `truant(squareForm) = 2` give β² < 2, so β ∈ {−1,0,1} (`Integer.square_below_two` over new `Natural.square_below_two`); the ONE entrywise proof is the decomposition `B = (I + β·Eᵀ) + (β·E + J_R·J_Rᵀ)` over the placed units `E = J_L·J_Rᵀ` (named indices `firstOfTwo`/`secondOfTwo` + bordered-vocabulary bridges); everything else is block ALGEBRA — `Eᵀ·E = J_R·J_Rᵀ`, `E² = 0` (new generic collapses `inclusionMatrix_transpose_multiply_self/disjoint` via `submatrix_identity_injective/disjoint` + `submatrix_pullback`), the shear `I + β·E` inverts pairwise (`shear_product_identity`, no determinant needed) and pulls x²+y² back to exactly the decomposition when β² = 1; β = 0 collapses to x²+2y² on the nose. Riders in matrix_ring: `multiply_zero`/`zero_multiply`/`scale_add`/`scale_zero_matrix`. Frictions filed (inbox): ring treats `(2:ℤ)`-as-cast as an opaque atom; disjunction-injection pays deep defeq per wrong ground disjunct (3 accepted expensive-step warnings); flex `select(q)` patterns don't δ-align constant arguments (workaround: unfold-first defeq steps).
- `S3.E4` `[x]` (M) The rank-3 escalators (explicit deduplicated list). — owes: S3.E2, S2.R4 · **DONE 2026-07-20:** the arithmetic
  interface for both rank-2 parents is complete (`Algebra/rank_two_truants.math`, manifest-added): `x²+y²` has truant 3 and
  `x²+2y²` has truant 5, with representation-only characterizations and elementary small-square nonrepresentation proofs.
  The coordinate boxes are now explicit (`Algebra/rank_three_escalation_bounds.math`, manifest-added): borders above `x²+y²`
  lie in `{-1,0,1}²`, while borders above `x²+2y²` first lie in `{-2,…,2} × {-3,…,3}`. The coupled positive-definiteness
  inequality is now formal: **`2a² + b² < 10`**, proved by evaluating the bordered form at the integral eliminating vector
  `(-2a,-b,2)` (the concrete Schur-complement calculation, without exposing an adjugate). It cuts the raw 35 pairs to exactly
  **23**, recorded in three symmetry bands by `squarePlusDoubleSquare_escalation_border_pairs`: `a=0` gives 7 values of `b`,
  `a=±1` gives 5 each, and `a=±2` gives 3 each. The **32 raw matrices are now materialized**, not merely counted:
  `sumOfTwoSquares_escalation_nine_candidates` and `squarePlusDoubleSquare_escalation_twenty_three_candidates` reconstruct
  every escalation as `borderedAssembly(parent, twoCoordinates(a,b), truant)`. The first actual ternary truant is now
  computed (`Algebra/rank_three_truants.math`, manifest-added at zero leaks): the zero-border candidate
  **`x²+y²+3z²` has exact truant 6**. Its leading block, zero border, corner 3, and split value formula are explicit; parent
  representations lift through the new generic `diagonalExtension_represents_parent`, the top basis vector gives
  `diagonalExtension_represents_corner`, and the nonrepresentation proof reduces `x²+y²+3z²=6` via `z²≤2` to the binary
  impossibilities at 3 and 6 (`Natural.six_not_sum_of_two_squares`,
  `Matrix.sumOfTwoSquaresForm_not_represents_six`). The next diagonal representative is also done:
  **`x²+y²+z²` has exact truant 7** (`Matrix.sumOfThreeSquaresForm_truant`); its failure at 7 reduces, according to
  `z∈{-2,-1,0,1,2}`, to the binary failures at 3, 6, and 7. `Matrix.isometric_isTruant` and
  `Matrix.isometric_truant_equals` make exact truants transport across each deduplication proof. The first actual
  deduplication orbit is now formal too: generic outer-product multiplication, the square-zero invertibility of
  `Matrix.topShear(v)`, and **`topShear_pullback_diagonalExtension`** prove the integral completion-of-squares identity
  `diag(A,c)[y↦y+tv] ≅ borderedAssembly(A,A·v,c+Q_A(v))`. Specializing to `A=I₂` shows that **all four raw borders
  `(±1,±1)` are isometric to `x²+y²+z²` and have truant 7** (`sumOfThreeSquaresForm_isometric_unitBorderCandidate`,
  `sumOfTwoSquaresUnitBorderCandidate_truant`). The remaining orbit is now complete too:
  **`x²+y²+2z²` has exact truant 14** (`sumOfTwoSquaresPlusDoubleSquareForm_truant`); the failure at 14 reduces,
  for `z∈{-2,-1,0,1,2}`, to the binary failures at 6, 12, and 14. A single parameterized isometry theorem,
  `sumOfTwoSquaresPlusDoubleSquareForm_isometric_oneUnitBorderCandidate`, handles every border with
  `a²+b²=1`, so all four `(±1,0),(0,±1)` candidates have truant 14. **All nine raw candidates over `x²+y²`
  are therefore classified into three proved orbits:** one zero-border form of truant 6, four two-unit-border
  forms of truant 7, and four one-unit-border forms of truant 14.

  **The 23 candidates over `x²+2y²` are now deduplicated to eight proved representatives**
  (`Algebra/rank_three_orbits.math`): the five diagonal forms
  `x²+2y²+cz²` for `c=1,…,5`, `x²+y²+z²`, and the two odd-border forms
  `x²+2y²+2yz+cz²` for `c=4,5`. The load-bearing theorem is the generic
  `topShear_pullback_borderedAssembly`, which sends a border `b` to `b+A·v`
  and adjusts the corner by `2⟨b,v⟩+Q_A(v)`; its isometry wrapper is
  `borderedAssembly_isometric_topShear`. The specialized
  `squarePlusDoubleSquareCandidate_isometric_shear` reduces every one of the
  23 admissible border pairs. The determinant-one odd case is identified
  with `x²+y²+z²`, and
  `squarePlusDoubleSquare_escalation_eight_representatives` packages the
  complete classification for arbitrary escalations of `x²+2y²`.

  **All eight representatives now have exact truants**
  (`Algebra/rank_three_representative_truants.math`, manifest-added at zero
  leaks): in the displayed order they are **14, 7, 10, 14, 10, 7, 7, 7**.
  The positive halves are compact witness tables gathered by `finite_check`;
  the negative halves reuse the binary classification below 16 and two
  parameterized diagonal/odd-border reduction lemmas. The theorem
  `squarePlusDoubleSquareRankThreeRepresentative_truant` packages the eight
  cases, and `squarePlusDoubleSquare_escalation_rank_three_truant` concludes
  that every escalation over `x²+2y²` has truant 7, 10, or 14. Together with
  `sumOfTwoSquares_escalation_rank_three_truant` (truants 6, 7, or 14), this
  completes the explicit rank-three escalation classification.
- `S3.E5` `[x]` (XL) ★★ The rank-4 escalators: machine-generate and dedup to the **207** selected isometry classes. — owes: S3.E2, S2.R4 · **DONE 2026-07-21:** every rank-four escalator is now kernel-proved isometric to one of the 207 selected normal forms; see the completion note below. The exhaustive classifier establishes that the selected list has 207 classes, while the kernel-critical downstream fact is the proved 207-way cover.
  **PILOT COMPLETE 2026-07-21:** `Algebra/rank_four_pilot.math` and the deterministic
  `scripts/generate_rank_four_pilot.py` carry one ternary branch end to end. Above
  `x²+y²+z²` (truant 7), positive-definiteness gives the exact coupled bound
  `Q(b) < 7`; the untrusted search finds 81 integer borders and seven squared-norm
  classes. The generated module kernel-checks all 81 top-shear reductions and all
  21 pairwise determinant separations. More importantly, the hand-written theorem
  `sumOfThreeSquaresRankFourEscalation_classified` classifies an arbitrary actual
  escalation into those seven classes, so coverage does not trust the enumerator.
  Normal verification measured about 9.1 s for the reusable foundation and 0.2 s
  for the 102 generated certificates with warm imports (31.4 KiB + 40.5 KiB source).
  This validates the search/certificate split. It does **not** check off E5: the
  remaining ternary parents require canonical reduction modulo `b ↦ b + A·v`, not
  the identity-parent shortcut that makes squared norm a complete invariant here.

  **SECOND BRANCH COMPLETE 2026-07-21:** the non-identity diagonal parent
  `x²+y²+3z²` (truant 6) is now classified end to end in
  `Algebra/rank_four_diagonal_branch*.math`, generated by the deterministic
  `scripts/generate_rank_four_diagonal_branch.py`. Positive-definiteness at the
  integral vector `(-3a,-3b,-c,3)` gives the exact coupled bound
  **`3a²+3b²+c² < 18`**. It leaves 109 raw borders. Top shears kill the first
  two coordinates and reduce the third modulo 3, producing 18 certified normal
  forms `(residue, corner)` with residue `-1,0,1` and corner `1,…,6`.
  `sumOfTwoSquaresPlusTripleSquareRankFourEscalation_classified` proves coverage
  for an arbitrary actual escalation: it reconstructs the border from its three
  coordinates, derives the finite box `[-2,3) × [-2,3) × [-4,5)`, invokes the
  generated classifier, and rewrites back to the original matrix. The 225 box
  leaves are gathered by explicit `Integer.AllFrom` certificates rather than
  auto-search; this reduced the collector build from 76 s to about 9 s and
  eliminated expensive-proof warnings. A cold whole-library build and the full
  test suite pass.

  The initial number 18 was a **top-shear normal-form bound**, not an isometry
  count. The later reusable diagonal sign-change certificate pairs the two
  nonzero residue bands, so the public coverage theorem now exposes at most
  12 alternatives. Larger parent automorphisms may still identify more.

  **DIAGONAL FAMILY FACTORED 2026-07-21:**
  `Algebra/rank_four_diagonal_family.math` now proves the symbolic coordinate
  action and value formula for `diag(1,1,d)`, the generic top-shear reduction,
  and the fraction-free coupled bound
  **`d a² + d b² + c² < d t`** from the single integral test vector
  `(-da,-db,-c,d)`. Thus later diagonal branches no longer copy the large
  Schur calculation. Its `x²+y²+2z²` specialization is now the certified
  319-border, 25-form branch described below; the invariant
  `2·corner-residue²` separates its displayed forms.

  **ALL PARENT BRANCHES COVERED 2026-07-21:** the search prediction above is
  now certified, and the same architecture has been carried through every
  remaining ternary parent. `x²+y²+2z²` has 319 admissible borders and exactly
  25 determinant-separated top-shear forms. The generic
  `Algebra/rank_four_weighted_diagonal_family.math` covers the five
  `diag(1,2,d)` parents (`d=1,…,5`): its shared fraction-free bound is
  `2d a²+d b²+2c² < 2dt`, and the five generated branches certify 1,877 raw
  borders. The first parent-automorphism pass is now certified by
  `Algebra/rank_four_parent_automorphisms.math` and
  `Algebra/rank_four_weighted_diagonal_orbits.math`: a symmetric integral
  automorphism of a parent lifts block-diagonally to every bordered child, and
  reflecting the `d`-weighted coordinate followed by a top shear reduces the
  five lists from 287 to 206 forms. The equal-weight coordinate swap for
  `diag(1,2,2)` then cuts its branch from 25 to 18, leaving **199** weighted
  branch alternatives altogether (25+18+36+68+52). The same swap identifies
  all 25 `diag(1,2,1)` representatives with the already-classified
  `diag(1,1,2)` representatives, so this branch contributes no new global
  classes. The two odd parents
  `x²+2y²+2yz+Cz²`, `C=4,5`, use the adjugate bound
  `(2C-1)a²+(C-1)b²+(b-c)²+c² < 7(2C-1)`; centered lattice reduction and
  border-sign isometry certify 444 borders and leave 26+32 alternatives.
  The earlier `d=3` diagonal branch has also been reduced from 18 to at most
  12 alternatives by a reusable signed-coordinate isometry.

  Every generated reduction, excluded box leaf, and finite collector is
  kernel-checked. The deterministic renderings are now a permanent
  `make rank-four-generated-check` gate. Summed over the ten distinct ternary
  parents, the global coverage predicates now name **276 distinct
  representatives**.

  This finished the first **coverage** substage of E5. The 276 alternatives
  are not pairwise non-isometric. The deterministic discovery
  tool `scripts/classify_rank_four_normal_forms.py` now reconstructs their
  concrete Gram matrices and proves the search exhaustive: for each potential
  isometry it enumerates every vector of the required norms inside exact
  adjugate/determinant coordinate bounds, then every compatible unimodular
  basis. Determinant and the theta-series prefix through 15 are only safe
  prefilters. The result is exactly **207 integral-isometry classes**, with
  **69 explicit unimodular identifications**, including all cross-parent
  coincidences.

  **GLOBAL DEDUPLICATION COMPLETE 2026-07-21:**
  `Algebra/rank_four_isometry_certificates_generated.math` replays all 69
  discovered congruences in the kernel. Each proof checks an explicit
  unimodular 4×4 matrix, its explicit two-sided inverse, and the full pullback
  action. `Algebra/rank_three_global_classification.math` first joins the two
  binary-parent branches into nine canonical ternary parents, using the new
  general theorem `escalation_transport_parent_isometry` rather than assuming
  a parent is literally canonical. The generated selected-normal-form and
  branch-coverage modules then merge all 276 historical alternatives into 207
  names. Finally **`Matrix.escalator_rank_four`** proves that every actual
  rank-four escalator satisfies `Matrix.IsRankFourEscalatorRepresentative`.

  The deterministic renderings, the counts 276/207/69, and all certificates
  are guarded by `make rank-four-generated-check`. The kernel proves the
  207-way cover and every positive identification. The claim that 207 is
  minimal still uses the exhaustive external non-isometry search (exact finite
  coordinate bounds plus determinant/theta prefilters); formalizing all
  pairwise negative certificates is not needed by downstream Fifteen-Theorem
  arguments and is recorded as an optional audit rather than an E5 blocker.
- `S3.C1` `[~]` (M) ★ The set of truants occurring anywhere in the tree is exactly **{1,2,3,5,6,7,10,14,15}**. — owes: S3.E3, S3.E4, S3.E5, S5.U2, S5.U3

  **LOW-RANK AND EXCEPTIONAL FINITE CASES COMPLETE 2026-07-21:**
  `Algebra/critical_truants.math` proves in the kernel that rank-zero through
  rank-three escalators have truants in `{1}`, `{2}`, `{3,5}`, and
  `{6,7,10,14}` respectively.  The theorem transports the exact truant of
  each canonical representative across the isometries supplied by the rank
  classifiers; it does not merely classify the underlying matrices.

  A complete value sweep through 15 over the 207 selected rank-four forms
  isolates exactly six finite exceptions.  `Algebra/rank_four_exceptional_truants.math`
  and its deterministic generated companion prove that two have exact
  truant 10 and four have exact truant 15.  The positive halves are explicit
  witness tables; the negative halves complete squares, bound two coordinates,
  and reduce to a small checked table of values missed by `x²+2y²`.

  `Algebra/rank_four_short_values.math` and its deterministic generated
  certificate chunks now close the complementary side in the kernel as well:
  each of the other 201 selected normal forms has an explicit witness for
  every value from 1 through 15 (3,015 witnesses in total).  The packaged
  theorem `Matrix.escalator_rank_four_short_value_classification` says that
  every rank-four escalator either has exact truant 10 or 15, or represents
  all fifteen test values.  Generation is untrusted; every scalar computation,
  existential witness, finite-range collection, selected-form case, and
  isometry transport is replayed by the kernel.  The certificate tables are
  split into small modules so the standard parallel build and incremental
  cache can check them independently.

  The remaining obligation is therefore precise: upgrade the through-15
  certificates for those 201 forms to universality, and prove the rank-five
  escalations of the six exceptional forms universal.  Those are the contents
  of `S5.U2` and `S5.U3`, so they remain dependencies here.  In particular,
  rank four can repeat the old truant 10; the earlier claim that every
  non-universal rank-four form must have truant 15 was too strong and is
  corrected here.
- `S3.C2` `[ ]` (L) ★★ **Master reduction:** if `Q` represents the nine critical numbers then `Q` is universal — via: a non-universal `Q` would embed an escalator missing its truant ∈ {nine}. *(Depends on rank-4 universality, Stage 5.)* — owes: S3.C1, S3.E5, S5.U2

---

## Stage 4 — Ternary representation theory (deep core)

*Goal: for each ternary section used in Stage 5, prove exactly which integers it represents.*
*Library note: **p-adics are not currently in `library/`** (removed) — block **4·P** re-introduces them. The existing feeders are `IntegerMod/` (ℤ/pᵏ, and F_p at a prime), `FiniteField/`, `Polynomial/`, and `Rational/`. As of 2026-07-18 the `IntegerMod/` feeder is substantially richer than when this sheet was written: Euler–Fermat, Wilson, √−1 mod p ≡ 1 (mod 4), the F_p field instance — and `GaussianInteger/fermat_two_squares.math` (Freek #20) is proved, which is the two-squares prototype of exactly the `S4.S*` escape-hatch style.*

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
> - **Route note 2026-07-18: prove Davenport–Cassels EARLY** — it is elementary
>   descent (days, not weeks), and it upgrades the escape hatch for every
>   *Euclidean* ternary (rational representation ⇒ integral) before any
>   commitment to genus theory. The 4·G gate then holds strictly behind the
>   E5 route-tagging pass: every ternary section tagged congruence-only /
>   Davenport–Cassels / genuinely-needs-genus, and 4·G paid only for the
>   third bucket. The ℚ_p construction itself (4·P) is low-risk
>   different-muscle work — interleave it during combinatorial-pole blocks
>   rather than queueing it.

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
- `S4.N1` `[~]` (XL) ★★ **Three-squares theorem**: `n = x²+y²+z²` ⇔ `n ≠ 4^a(8b+7)`. The current route needs rational representability, via `S4.G1` or a direct Dirichlet/Minkowski construction, followed by the completed Aubry–Davenport–Cassels descent; it no longer needs `S4.G0/G2` for this particular form. — owes: S4.G1 **or** external · **OBSTRUCTION DIRECTION DONE 2026-07-21:** `Algebra/three_squares_obstruction` and its deterministic generated companion prove that a sum of three squares is never 7 modulo 8. `Algebra/three_squares_descent` proves that divisibility of a three-square sum by 4 forces all roots even; `Algebra/three_squares_power_descent` cancels the resulting factor; and `Integer.four_power_times_eight_plus_seven_not_three_squares` iterates the descent for every exponent. The theorem is also lifted to `Matrix.sumOfThreeSquaresForm`. `Algebra/three_squares_theorem` now packages the forbidden-shape predicate, the open converse, and the final characterization. `Algebra/three_squares_obstruction_arithmetic` plus the seven `three_squares_residual_cover_*` modules prove that this one converse supplies every residual cover for `d=1,…,7`; no additional arithmetic lemma is needed for the seven-form pilot family once the converse lands. **RATIONAL-TO-INTEGRAL DESCENT DONE 2026-07-21:** `Algebra/three_squares_rational_descent` clears three rational denominators, uses balanced residues and the other intersection of a line with the sphere to reduce a positive denominator strictly, and closes by strong induction. `Rational.ThreeSquaresConverse` now isolates the remaining arithmetic statement, while `Matrix.three_squares_converse_of_rational` turns it directly into the matrix converse. Thus the integral-regularity step is complete without genus or ℤₚ-lattice theory; only existence of the admissible rational point remains open. **Performance note:** nested substitution through small case trees can take minutes. Factoring claims into closed helpers, replacing broad `substituting` with targeted `Equality.congruence`, and explicitly unpacking witnesses reduced the same certificates to roughly one second; the residual cases are split into independent modules so incremental and parallel builds retain that gain.
- `S4.S*` `[~]` (M each) ★ For each ternary section `T_i` from `S3.E5` (`x²+y²+2z²`, `x²+2y²+2z²`, `x²+y²+3z²`, …): its exact represented-set, via **(a)** `IntegerMod/` congruences (escape hatch), **(b)** `S4.G2` regularity, or **(c)** direct argument. *(Tag each section with the route it actually needed.)* — owes: S4.L3, plus per-section S4.G2 / `IntegerMod/` · **PARITY REDUCTIONS DONE 2026-07-21:** `Algebra/three_squares_parity_transforms` proves integrally that `x²+2y²+2z²` has exactly the same represented integers as `x²+y²+z²`, and that `x²+y²+2z²` represents `n` exactly when three squares represents `2n`. The proof divides three coordinates modulo two, selects a same-parity pair, and applies the identities `(u+v)²+(u-v)²=2u²+2v²` and `(x+y)²+(x-y)²+(2z)²=2(x²+y²+2z²)`. Both ternary represented-set problems therefore reuse `S4.N1` and need no independent genus argument; the rank-four forms above them still require their residual/congruence covers.
- `S4.Q1` `[ ]` (L) *(Alternative tail route)* Tartakowsky-type bound: a positive quaternary represents all **sufficiently large** integers meeting the local conditions — reduces each rank-4 universality to a finite check. — owes: S4.L3

---

## Stage 5 — Assembly and the finite computations

*Goal: per-escalator universality and the final theorem.*
*Library: Stage 0–4; relies on the kernel's computation/reflection for the bounded checks.*

- `S5.K1` `[ ]` (L) ★ Make `S3.T1`'s bounded representation check **compute efficiently in-kernel** to the bounds needed (the "rather large calculation"). *(Performance risk — prototype before committing; verify the kernel can discharge a few thousand bounded checks.)* — owes: S3.T1 · *Route note 2026-07-18: run a THROWAWAY SPIKE immediately after Stage 1, before any Stage-2 work — decide `Represents(A, n)` in-kernel for `x²` and `x² + y²` for all `n ≤ 15` by explicit box enumeration and measure wall-clock. The workload is quadratic-form evaluation at small integer points — pure ground arithmetic (never touches the determinant, so the Leibniz definition's computation-hostility is irrelevant), exactly the muscle the GMP ground-arithmetic tier (landed 2026-07-11) provides. The spike sorts K1 into "already works" / "needs the fast-numeral plan extended" / "needs reflection machinery" — three different futures. Ledger the measurement even if the probe code is deleted.* · **SPIKE RUN 2026-07-19** (`Test/fifteen_spike_test.math`, kept as a lock): all represented `n ≤ 15` for `x²` ({1,4,9}) and `x²+y²` ({1,2,4,5,8,9,10,13}) proved by explicit witnesses through `squareForm_represents_square` + new `Matrix.directSum_represents_sum` (integer_quadratic_form.math) — **10 concrete representation theorems + the general sum lemma verify in 34 ms wall-clock total** (single-file `kernel verify`, warm caches; ground ℤ facts like `3·3 + 2·2 = 13` decide instantly). Negative control: corrupting a value to `= 14` fails as expected (the false ground claim burns the prover's budget — false claims are SLOW, ~0.6 s, which matters for enumeration-by-failure designs). VERDICT: witness-supplied bounded representation is squarely "already works" — per-instance cost ≈ 3 ms, so thousands of bounded checks are minutes, not days. UNMEASURED: `decide`-style exhaustive search (no bounded-∃ decision procedure exists yet) — the negative side of S3.T1's check will need either the box-bound THEOREM route (PD ⇒ values outside a box exceed n) or a reflection-style search; the theorem route stays the default.
- `S5.U1` `[x]` (M) ★ Universality template: given a rank-4 escalator `L`, a ternary section `L3 ⊆ L` with known represented-set (Stage 4), and the 4th coordinate covering the residual exceptions ⇒ `L` universal. — owes: S1.S1, S4.S*, S5.K1 · **DONE 2026-07-21:** `Algebra/rank_four_pilot_universality.math` completes the square uniformly for the seven selected forms above `x²+y²+z²`, identifying them with `x²+y²+z²+d·w²` for `d=1,…,7`. `Matrix.ThreeSquareResidualCover(d)` is the exact arithmetic interface: every positive target is a represented three-square residual plus `d·w²`. The generic lift proves the diagonal form universal, isometry transports universality back to the bordered candidate, and `selectedRankFourPilot_universal` packages all seven cases. `Matrix.selectedRankFourPilot_universal_of_three_squares_converse` now discharges all seven covers from the single open `Matrix.ThreeSquaresConverse`; this closes the pilot arithmetic assembly conditionally, rather than leaving seven independent obligations. `Algebra/rank_four_completed_cover_universality.math` handles every other selected constructor with three fraction-free identities: `TwoSquaresScaledCompletedCover` covers the 32 triple/double forms, `WeightedCompletedCover` the 140 weighted forms, and `OddCompletedCover` the 28 odd forms. Each interface records the necessary congruence by naming the completed variable (for example `u=d·z+r·w`), proves the scaled identity by `ring`, cancels its nonzero determinant factor, and supplies the matrix witness. The four templates cover all 207 selected forms; no matrix algebra remains in the per-form universality stage. **FIRST NONPILOT COVERS DONE 2026-07-21:** `Algebra/rank_four_d2_zero_residue_universality` feeds the existing residual covers through the parity equivalence `x²+y²+z² ↔ x²+2y²+2z²`, proving the six selected forms `squarePlusDoublePlusScaledRankFourRepresentative(2,0,0,c)` for `c=2,…,7` universal from the same Three Squares Converse. **UNIT-RESIDUE COVERS DONE 2026-07-21:** `Algebra/rank_four_d2_unit_residue_universality` proves the four selected forms `squarePlusDoublePlusScaledRankFourRepresentative(2,1,1,c)` for `c=2,3,6,7` universal from the same converse. It packages the exact substitution `p=y+z+w`, `q=y-z`, proves the modulo-two compatibility needed to invert it, and uses the uniform obstruction residual `4^e(8b+7-d)` with `w=2^e` for `d=c-1∈{1,2,5,6}`. **THIRD-RESIDUE COVERS DONE 2026-07-21:** `Algebra/rank_four_d2_third_residue_universality` proves all six selected `squarePlusDoublePlusScaledRankFourRepresentative(2,0,1,c)` forms, `c=2,…,7`, universal. For `m≥c`, doubling and completing the square reduces to the odd `x²+y²+2z²` residual `2(m-c)+1`, whose double `4(m-c)+2` is automatically admissible for three squares; a modulo-two ordering lemma recovers the completed coordinates. The existing explicit through-15 tables cover `m<c`. **DOUBLE UNIT-RESIDUE COVERS DONE 2026-07-21:** `Algebra/rank_four_double_unit_residue_universality` proves all ten selected `sumOfTwoSquaresPlusScaledSquareRankFourRepresentative(2,1,c)` forms universal. Its completed identity is `2Q=(x+y)²+(x-y)²+(2z+w)²+(2c-1)w²`. If `2m=4^e(8b+7)`, parity forces `e>0`; choosing `w=2^(e-1)` leaves `4^(e-1)(32b+k)`, where the ten relevant `k` are all 1, 3, or 5 modulo 8. A general same-parity-pair lemma recovers `x,y,z`. **DOUBLE ZERO-RESIDUE COVERS DONE 2026-07-21:** `Algebra/rank_four_double_zero_residue_universality` uses `2Q=(x+y)²+(x-y)²+(2z)²+2c w²` to prove all twelve selected diagonal forms. Ten use fixed admissible even cores `2,4,6,8,10,12,14,18,20,24`; a reusable piecewise obstruction-resolver handles `c=6` by doubling `w` after its first branch and handles `c=14` with residuals `0,32,64` followed by core 12. Thus all 22 selected double forms are conditionally universal. A global coordinate-swap certificate identifies the otherwise-unselected `double.r0.c3` with `triple.r0.c2`, giving a 46th selected conditional universality proof without requiring the represented-set theorem for `x²+y²+3z²`. **TRIPLE ZERO-RESIDUE COVERS DONE 2026-07-21:** `Algebra/rank_four_triple_zero_residue_universality` makes Dirichlet's converse for `x²+y²+3z²`, with exceptional shape `9^a(9b+6)`, a separate explicit input. Its generic 9-adic core lemma handles diagonal coefficients 3, 4, and 5. For coefficient 6, the proof tests whether the inner quotient is exceptional and uses one of two fourth-coordinate scales, leaving a residual with core 4 or 7. Together with the coordinate-swap case, all five selected diagonal triple forms are conditionally universal. **TRIPLE UNIT-RESIDUE COVERS DONE 2026-07-21:** `Algebra/triple_squares_one_three_three` proves that a representation of `3n` by `x²+y²+3z²` descends modulo three to a representation of `n` by `x²+3y²+3z²`; it also packages the sign choice needed to solve `u=3z+w`. `Algebra/rank_four_triple_unit_residue_universality` then applies `3Q=(3z+w)²+3x²+3y²+(3c-1)w²`. The exceptional target has positive 9-adic exponent, and `w=3^(e-1)` leaves a uniform `3k+1` residual for every `c=2,…,6`. Thus all ten selected triple forms are conditionally universal from the single Dirichlet converse. **WEIGHTED D3 ZERO-RESIDUE COVERS DONE 2026-07-21:** `Algebra/rank_four_weighted_d3_zero_residue_universality` makes the classical converse for `x²+2y²+3z²`, with exceptional shape `4^a(16b+10)`, a third explicit ternary input. For coefficients `3,…,9`, subtracting `c(2^a)^2` leaves core `10-c`; a reusable 4-adic separation lemma proves the nonzero residue cores admissible, and the core 4 case extracts one more factor of four. Coefficient 10 uses residual 0 when `b=0`, a pure square when `b=1`, and `w=2^(a+1)` thereafter to leave core 2. All eight selected diagonal weighted-d3 forms are therefore conditionally universal, raising the selected total to 63. The remaining broader obligations are the three explicit ternary converses, the other arithmetic cover facts in S4.S*, and their generated 207-way assembly in S5.U2.
- **WEIGHTED D3 SECOND-UNIT COVERS DONE 2026-07-21:** `Algebra/rank_four_weighted_d3_second_unit_universality` isolates Dickson's converse for `x²+2y²+6z²`, with exceptional shape `4^a(8b+5)`.  For `squarePlusDoublePlusScaledRankFourRepresentative(3,1,0,c)`, completing the square gives `2Q=(2y+w)²+2x²+6z²+(2c-1)w²`; a parity lemma derives the integrality of `y` from the completed equation itself.  If `2m` is exceptional, its 4-adic exponent is positive and `w=2^(a-1)` leaves one of the odd cores `17,15,11,9,7,3,1`, none congruent to 5 modulo 8.  This proves all seven selected coefficients `c=2,3,5,6,7,9,10` conditionally universal and raises the selected total to 70.
- **WEIGHTED D3 THIRD-UNIT COVERS DONE 2026-07-21:** `Algebra/rank_four_weighted_d3_third_unit_universality` records the exact local converse for `x²+3y²+6z²`: the target must be a square modulo three and must avoid `4^a(16b+14)`.  Completing the selected forms gives `3Q=(3z+w)²+3x²+6y²+(3c-1)w²`; the completed equation itself supplies the modulo-three sign needed to recover `z`.  The concrete modules aggregated by `Algebra/rank_four_weighted_d3_third_unit_covers` prove all eight selected coefficients `c=3,…,10` conditionally universal.  Six use the uniform full- or half-scale covers.  The `c=5` proof separates the two small unscaled quotients before settling into core 6 or 10, while `c=9` separates 4-adic exponents zero, one, and at least two before settling into an odd core or core 6.  The selected total is now 78.
- **WEIGHTED D3 BOTH-UNIT COVERS DONE 2026-07-21:** `Algebra/rank_four_weighted_d3_both_unit_foundation` isolates Dickson's exact local converse for `2u²+3v²+6x²`: the target must be twice a square modulo three and must avoid `4^a(8b+7)`.  For `squarePlusDoublePlusScaledRankFourRepresentative(3,1,1,c)`, the identity `6Q=2(3z+w)²+3(2y+w)²+6x²+(6c-5)w²` supplies both integrality conditions needed to recover `y,z`; the modulo-three sign choice preserves the represented square.  If `6m` is obstructed, parity forces a positive 4-adic exponent and reduction modulo three forces the inner parameter positive.  Taking `w=2^(a-1)` leaves `4^(a-1)(32q+k)` with `k=53,41,35,29,17,11,5`, each visibly 1, 3, or 5 modulo 8.  The import-only `Algebra/rank_four_weighted_d3_both_unit_covers` aggregates the seven selected coefficients `c=2,4,5,6,8,9,10`, raising the selected conditional total to 85.  Every new proof also passes the cite-only 1000-step gate; the one-theorem concrete modules avoid the current same-module auto-prover-pool blow-up.
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
