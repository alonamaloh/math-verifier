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

## The ladder, and the deep-search-as-error-message idea

**Status 2026-07-30: cap 6 is GREEN.** Walking the cap down and treating each
break as a proof to improve works, and the fixes are improvements:

| prove cap | files failing | state |
| --- | --- | --- |
| 6 | 3 → **0** | done — three proofs written out |
| 3 | 16 → **11** | in progress — every break dictates its own fix |
| 1 | 35 | the goal; worth 14.9 s → 6.4 s on the profiled file |

The three fixed: `Natural/distance.math` (`le_add_distance` was hiding
`distance_succ_succ` plus an associativity shuffle behind a bare `done by`),
`Natural/cancellation.math` (a by-less chain step hiding successor-multiply
unfolded on both sides), `Natural/binomial.math` (a by-less `≤` step hiding
`Natural.le_successor` and a transitivity). All three now name what they use,
which is what the style guide asks for anyway.

### Lowering the cap: the theory pans out, but the fixes are not all trivial

At cap 3, **14 files failed and 14 of 14 explained themselves** — every break
named the exact lemma the deeper search used. That part of the theory is
confirmed outright: the messages remove all the reverse-engineering.

The fixes split into two classes, and only one is mechanical.

**Mechanical (fixed, 4 sites).** A bare claim whose rewrite is a single named
equation. Every one of these was the same shape:

```math
¬(1 + k = 0);                                    -- before
¬(1 + k = 0) by substituting Natural.one_add;    -- after
```

`Natural/binomial.math`, `Integer/integral_domain.math`,
`Polynomial/units.math` all took exactly that edit.

**Not mechanical.** Fixing the first site in a file usually moves the failure
to a *second* site in the same file, and the later ones are real proof edits.
`Natural/binomial.math` after its easy fix reports

```
calc step 2 at line 125
  The deeper search rewrote with:
    - local binder _claim_anon_118_9
    - library lemma Natural.binomial_pascal
```

— a calc step that needs an anonymous local claim AND Pascal's rule. The
message says *what was used*, not *how to restructure the step*; turning that
into named steps is ordinary proof work.

**Then the trace was extended to carry the intermediate STATEMENTS, and the
surgery became mechanical too.** The message now reports the full route — every
rewrite, in the order an author states them, with the goal each one produced:

```
  It got there in 2 rewrite(s). Stating the intermediate forms makes a
  shallow search enough — in this order:

      (successor dPredecessor) + (Natural.triangular dPredecessor)
          = (Natural.triangular (1 + dPredecessor));
      (Natural.triangular (1 + dPredecessor))
          = (successor (dPredecessor + (Natural.triangular dPredecessor)))
          by substituting `Natural.successor_add`;
  and then the claim itself follows by substituting `Natural.one_add`.
```

`Natural/pairing.math` was fixed by transcribing that **verbatim** — the three
lines above became the three lines of the proof, and the site now passes both
capped and uncapped. That is the loop working end to end: the elaborator finds
the multi-step argument and dictates the declarative form of it.

Recording details that matter:

- The step is recorded **after the transport typechecks**, not when the rewrite
  is attempted. A rewrite rejected by that typecheck was never part of the
  route, and reporting it sends the author after a step the search did not take.
- `deepRoute_` is innermost-FIRST, because a nested success completes before
  its caller records — which is already the order the author writes the
  intermediate forms in, so no reversal is needed.
- Equation names are printed through `citableNameFromFactSource`, so they are
  paste-ready (`Natural.one_add`, not `library lemma Natural.one_add`). An
  anonymous fact has no citable name and is printed raw — correctly, since it
  has to be *stated* rather than cited.

**Second iteration: record every rewriter, not just the bridge.** The first
version traced `contextEqualityBridge` only, and on a `by substituting` site it
reported one rewrite whose "intermediate form" was **already written in the
proof** — true but useless, because the steps that path performed itself were
invisible. `elaborateClaimBySubstitution` now records its own rewrites into the
same route, and each step carries how the goal it produced was closed. The same
site went from 1 reported rewrite to 3, and transcribing the missing one fixed
it.

**Third iteration: the long routes were partly inflation.** Reported lengths
were 1,1,1,1,2,2,5,5,5,8,**11** — but the 11 was an artefact. The retry
re-elaborates the WHOLE declaration, so the collected steps were every rewrite
anywhere in it: that "route" spanned two unrelated `case` arms of the same
theorem. Each step now records the line of the claim it was performed for, and
the report keeps only the steps matching the failing line. The 11 became **2**,
and the honest distribution is 1,1,1,1,2,2,2,5,5,5,8.

That site (`Natural.binomial`, a calc step) was then fixed by transcription:
its two-step route named the two anonymous claims it leaned on, and giving them
names plus two explicit calc steps closed it, capped and uncapped.

Anonymous facts are now reported usefully too. A route step through an unnamed
claim used to print its internal binder (`local binder _claim_anon_120_9`),
which is neither citable nor meaningful; it now reads *"the (unnamed) claim at
line 120 — give it a name and cite it"*, which is exactly the fix.

Naming matters as much as recording. Every equation is printed as the author
would type it: `citableNameFromFactSource` for context/library facts, and for a
`by substituting` candidate the lemma is pulled out of its provenance label,
since otherwise the suggestion reads ``by substituting `supplied via `by
substituting```.

Ladder: cap 3 is **14 → 11 files**, all 11 carrying a full trace. Then ~34 at
cap 1. A transcription rather than an investigation.

### Deep search as an error-message generator — BUILT 2026-07-30

Working. When the equality bridge is capped and a declaration fails, the
elaborator re-elaborates it **once, uncapped, on the failure path only**; if
that succeeds, the step was doing several rewrites at once, and the message
names the equations the deeper search used:

```
library/Algebra/aggregation.math:195:1: elaborate error: calc step 1 at line 195
  …
  NOTE: this DOES elaborate when the equality bridge is allowed to chain more
  rewrites than the current cap permits, so a step here is doing several
  rewrites at once and the proof would say more if they were named.
  The deeper search rewrote with:
    - library lemma Natural.add_associative
    - library lemma Algebra.indexedAggregate_add_one
  State each rewritten form as its own claim, or cite the equation directly
  with `by substituting <eq>`.
```

That is the whole point of the ladder: each of the ~34 remaining cap-1 breaks
now *explains itself*, instead of having to be reverse-engineered.

**Design notes, all of them earned by getting it wrong first.**

- **Hook at the TOP STATEMENT, not the claim.** A step can fail on several
  paths — a structured claim, a **calc step**, a coercion — and only the top
  statement sees all of them. The fixture that finally exercised this
  (`Algebra/aggregation.math`) fails in a *calc step*, so a claim-level hook
  came up empty. The message is appended to the original error, which already
  carries the precise line, so coarse hooking costs no precision.
- **The "cap bit here" counter needs the STATEMENT's lifetime.** Two earlier
  attempts keyed it to the prover's armed frame, which is entered only for the
  outermost claim and is therefore already stale when a nested arm reports.
- **Gate the retry on the counter, not on failure alone.** Speculative probes
  fail constantly; retrying each uncapped would be catastrophic. `inDeepRetry_`
  additionally stops the retry re-entering itself.
- **Inert by default.** With the cap unlimited (the default),
  `bridgeDeclines_` never increments, so the retry never runs and the happy
  path pays nothing.
- **Build the fixture before the feature.** A site that fails *while* the cap
  is set is not the same as one that fails *because of* it — at cap 1 many
  files fail for unrelated reasons. I mistook one of those for a non-firing
  feature twice. The fixture procedure that works: run the full library at
  cap 1 with `make -k`, then re-verify candidates STANDALONE both capped and
  uncapped, and keep only those that pass uncapped and fail capped.

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
