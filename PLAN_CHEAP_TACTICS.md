# Cheaper tactics: a design exploration

Written 2026-07-30, after one successful optimisation and four failed ones.
The failures are the useful part: they rule out tuning, and they say what kind
of change is actually required.

Companion to `PERF_EXPENSIVE_DECLARATIONS.md`, which holds the measurements.

## What is measured, not assumed

- Claim self-time across a cold `make library`: **910 s** over 2757 claims.
- It is **concentrated**: the top 10 claims were 46% of the total before the
  `by substituting` fix.
- In every expensive declaration profiled, the dominant cost is a rung that
  **loses**. On `Metric/connected.math`, `contextEqualityBridge` is 74
  invocations, **one win**, 10.4 s of the file's 24 s.
- The one fix that worked — a cheap-prover pass in `by substituting` — worked
  because a cheap winner existed and was being found *after* an expensive
  loser had spent the budget. 189 s → 1.4 s on the worst site.

## Four failed attempts, and the single thing they prove

| attempt | result |
| --- | --- |
| Lazy goal forms in the substitution path | 2% — noise. Reverted. |
| Cheap-pass-first on `contextEqualityBridge` | **Worse**: 14.7 s → 15.6 s |
| Cap the bridge's recursive prove by kernel steps | 4.9 s but **4 files break**; at 200k/400k green but **zero gain** |
| Cap the number of recursive proves per bridge call | caps 1/2/3/6 → **3–6 files break**, and cap 6 gives no gain |

Every discriminator tried is a **budget**: steps, passes, counts. All of them
fail the same way, and the pattern across them is the finding:

> The searches that must be allowed and the searches that waste time are **not
> separated by how much they cost**. A cheap bound removes wins; a bound loose
> enough to keep the wins removes no waste.

Cheap-pass-first is worth understanding separately, because it is the shape
that *did* work elsewhere: it helps only when a **cheap winner exists**. At a
1-in-74 win rate there is almost never a cheap winner to find early, so the
extra pass is pure overhead. **A fix's shape does not transfer between rungs
with different win rates.**

## The architectural diagnosis

`contextEqualityBridge` is not congruence closure. For each equality `a = b`
in context, and each direction, it rewrites occurrences in the goal and then
**calls the full auto-prover recursively on the rewritten goal**. Transitivity
is not enumerated; it emerges only because that recursive prove can re-enter
the bridge. One candidate rewrite spawns a whole search, which spawns more.

Generalising: **in this elaborator, search is the default.** The auto-prover
ladder runs on every by-less claim, and again inside premise discharge for
every hint. A `by <Lemma>` does not mean "check this"; it means "check this,
and search for whatever it needs".

The contrast worth borrowing from is that in Lean 4 the default is the
opposite. Its everyday tactics are **directed and fail fast** — `exact` checks,
`rw [h]` rewrites left-to-right at the first match and fails if it does not
apply, `simp only [h₁, h₂]` is confined to a stated lemma set. Search exists —
`aesop`, `exact?` — but it is **opt-in, separately named, and given an explicit
rule set**. Nothing searches merely because a step was written down.

That is the difference this codebase's profile keeps reporting.

## Proposals, ranked by (expected value × confidence)

### A. `by <tactic> using [lemma, …]` — a restricted citation

Directly the "use this tactic with only these lemmas" idea, and the closest
analogue of `simp only [h₁, h₂]`. The author states the search space; the
elaborator does not go looking beyond it.

```math
piece ⊆ whole by substituting using [Plane.orientSegment_reversed];
x ∈ region     by prover using [Set.member_union, Set.singleton_member];
```

Why this is first: it is **additive** — no existing proof changes meaning, so
it cannot break the library — and it converts the expensive sites one at a
time with the author in control. It also improves the proofs as documents,
which is the project's actual goal; today `by <Lemma>` understates what the
step costs, and this makes the real dependency visible.

Open question worth settling early: does `using [...]` restrict the *whole*
sub-search, or only the top rung? Restricting the whole sub-search is what
makes it cheap, and is what `simp only` does.

### B. A directed rewrite that does not search

`by substituting <eq>` currently tries both directions, subsets of
occurrences, and then the full prover on each candidate. That is a search
wearing a rewrite's name — and it is 100% of the cost at the sites profiled.

Add a rewrite with `rw` semantics: **one direction, all occurrences, close by
cheap rungs only, fail loudly otherwise.** Most existing uses would move to it
unchanged. Keep today's searching form under its own name for the cases that
genuinely need it.

Confidence high that this is cheap; medium on how many sites can move without
hand-editing. Measure by converting `Plane/Graph/orient.math` first.

### C. Congruence closure for the equality bridge

The principled fix, and the one the user's own mental model already assumes: a
union-find over the context equalities with congruence propagation, answering
"are these two terms equal by the known equations" in near-linear time instead
of by recursive proof search.

Highest ceiling — it would make the dominant losing rung cheap everywhere
rather than at one site — and the largest change. It also **subsumes** most of
what the bridge is reached for, so it may allow the recursive-prove path to be
narrowed afterwards, which is the thing no budget could safely do.

Worth prototyping behind an env flag and comparing win-for-win against the
current bridge on the library before committing to it.

### D. Discrimination-tree indexing for candidate selection

`contextFactMatch` already has a `spineHash` prefilter and a similarity score.
The bridge appears not to. Head-indexed candidate selection is standard and
contained.

**Caveat, measured:** equations whose endpoint does not occur in the goal are
*already* free — the occurrence search returns zero and the candidate is
skipped. So indexing helps the scan, not the thing that dominates. Do this for
tidiness, not as a performance fix.

### E. Make search opt-in

The largest change, and the one the profile keeps pointing at: a by-less claim
runs the full ladder, and so does every hint's premise discharge. If a claim
had to *ask* for search — bare statements closing only by cheap, directed
rungs — the pathological sites would become errors that name themselves
instead of 190-second successes.

This is a language-policy change, not a tactic change, and it would touch every
file. Not a next step; the thing A–C are incrementally walking toward.

## Recommended order

1. **A**, because it is additive, cannot regress anything, and lets us convert
   the known-expensive sites deliberately.
2. **B**, measured on `orient.math` and the `segment_order` family.
3. **C** as a prototype behind a flag, compared win-for-win before adoption.

D is tidying. E is the destination, not a step.

## Rules earned the hard way

- **Measure serially.** `-j 16` wall-clock per claim is contended: the same
  declaration measures 13–16 s parallel and 9.7 s serial. A before/after
  across the two is meaningless.
- **Iterate on a middling case, not the worst one.** The 189 s outlier costs
  three minutes per attempt; a 9 s case of the same shape costs seconds and
  tells you the same thing.
- **Grep the build for `error`, never for the thing you are editing** — and
  never let `head` truncate the stream you are checking.
- **A fix's shape does not transfer between rungs with different win rates.**
