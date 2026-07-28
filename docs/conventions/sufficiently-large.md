# "For sufficiently large *m*"

How to state and use eventually-facts, and their spatial twin "for all *y*
sufficiently near *x*". Written for a mathematician: it assumes analysis and
assumes nothing about proof systems.

*(Part of the project conventions; see `LANGUAGE.md` for the index.)*

## The phrase you already write

In a limit argument you say

> Since sₘ → L, we have |sₘ − L| < ε/2 for all sufficiently large m.

and a line later you use two or three such statements *at the same m* without
comment. What you did silently is take the largest of the thresholds. Nobody
writes that down, because nobody needs to — a reader knows that finitely many
eventually-statements hold together eventually.

This system works the same way, for the same reason. You state the facts, you
open a block, and inside the block they are all available at one index. No
threshold is ever named and no maximum is ever taken.

## Stating one

Write it as you'd say it, index bound up front:

```math
eventually (m). abs(s(m) - limit) < ε
```

Read: "from some index on, |s(m) − limit| < ε". Underneath it is
`∃ N. ∀ m ≥ N. …`, but you will rarely have to think about the N.

This is an ordinary statement, so it can be a hypothesis, a conclusion, or a
fact asserted mid-proof. Convergence is *defined* this way
(`library/Real/convergence.math`):

```math
definition Real.SequenceConverges (s : ℕ → ℝ) (limit : ℝ) : Proposition :=
  ∀ (ε : ℝ). ε > 0 →
    eventually (m). abs(s(m) - limit) < ε
```

To get one out of a hypothesis, state the fact you want and name the
hypothesis as the reason:

```math
eventually (m). abs(s(m) - sLimit) < ε / 2 by sConverges;
```

Note what you did *not* write: `sConverges` applied to `ε / 2` and to a proof
that `ε / 2 > 0`. Naming the hypothesis is enough, provided `ε / 2 > 0` is
already on the page above. Throughout this system, you cite the fact and let
its side conditions be picked up from what you have already said.

## Proving one: the block

To prove a statement of the form "eventually …", open

```math
for m sufficiently large: { … }
```

Inside, `m` is your index, and **every eventually-fact standing above is
available at that same m**, as an ordinary fact to cite or chain against.

Here is the limit of a sum, complete and unabridged
(`library/Real/limits.math`):

```math
theorem Real.SequenceConverges.add (s t : ℕ → ℝ)
        (sLimit tLimit : ℝ)
        (sConverges : Real.SequenceConverges(s, sLimit))
        (tConverges : Real.SequenceConverges(t, tLimit))
        : Real.SequenceConverges((n : ℕ) ↦ s(n) + t(n), sLimit + tLimit) := {
  take ε : ℝ;
  suppose ε > 0;
  ε / 2 > 0;
  eventually (m). abs(s(m) - sLimit) < ε / 2 by sConverges;
  eventually (m). abs(t(m) - tLimit) < ε / 2 by tConverges;
  for m sufficiently large: {
    abs((s(m) + t(m)) - (sLimit + tLimit))
       = abs((s(m) - sLimit) + (t(m) - tLimit))
             by substituting
                 (ring : (s(m) + t(m)) - (sLimit + tLimit)
                     = (s(m) - sLimit) + (t(m) - tLimit))
       ≤ abs(s(m) - sLimit) + abs(t(m) - tLimit)
       < ε / 2 + ε / 2
       = ε
  }
}
```

That is the entire proof, and it is the proof you would write on a board:
take ε, halve it, quote convergence twice, triangle inequality. The two bounds
used inside the block are the two facts stated above it, delivered at m. There
is no threshold and no maximum anywhere in the text.

When the body is a single calculation the braces are optional:

```math
for m sufficiently large:
  abs(t(m) - limit)
     = abs(s(m) - limit)   by pointwiseEqual(m)
     < ε
```

## Getting a plain fact out of the block

Often what you conclude does not mention m at all: two limits are equal, some
quantity is below ε. Then you have proved "eventually, C" where C says nothing
about the index, and what you want is just C. Say so:

```math
eventually (m). abs(L1 - L2) < ε
    by for m sufficiently large: { … };
done by Natural.Eventually.constant
```

`Natural.Eventually.constant` is the sentence *if C holds for all sufficiently
large m and C does not mention m, then C* — the step you take without noticing.
`Real.SequenceConverges.unique` (`library/Real/convergence.math`) is this in
full: three lines of set-up, a block, and that closer.

If instead you are deriving a contradiction, prove "eventually, False" and
close with `Natural.Eventually.not_eventually_false`: there is no index left
for it to hold at. `Plane.value_bounded_above`
(`library/Plane/extremum.math`) ends exactly that way.

## Facts that are not obviously "eventually"

Three more things join the block, and knowing them is most of what makes this
usable.

**"m is past this particular index."** If your argument needs `scale ≤ m` for
some `scale` produced earlier, that is itself an eventually-fact:

```math
eventually (k). scale ≤ k by Natural.Eventually.beyond;
```

It now folds in with the others and you still take no maximum. This is the
move that turns a two-fact argument carrying a hand-made `max(threshold, scale)`
into a three-fact argument carrying nothing.
`MetricSpace.equal_limits_of_closing` (`library/Metric/separation.math`)
combines two convergence tails and one of these.

**A fact that simply always holds** is eventual for free — state it inside the
block, nothing special needed.

**A fact at a shifted index** — see the next section.

## The one restriction

Inside the block your facts arrive **at m and at no other index**. If the
argument needs |s(m+1) − L| < ε, or the fact at some f(m), the block will not
hand it to you.

For a fixed offset, `Natural.Eventually.shift` moves an eventually-fact along:
from "eventually P(m)" it gives "eventually P(offset + m)". For anything else
you are outside what this construct does. **Say so plainly rather than bending
the argument to fit** — a natural proof the system won't accept is a defect
worth reporting, not a proof to rewrite.

One neighbouring snag with a mundane cause: if you write `let deep := index(k)`
inside the block, facts that arrived *about* `index(k)` are not automatically
seen as facts about `deep`. Restate them once at `deep`. That is about `let`,
not about "eventually".

## The same idea for points instead of indices

"For all y sufficiently near x" behaves identically, with a radius where the
index had a threshold — and the *smaller* of two radii where indices took the
*larger* of two thresholds. Continuity of a sum
(`library/Real/continuity.math`):

```math
MetricSpace.Near(x, (y : ℝ) ↦ abs(f(y) - f(x)) < ε / 2)
    by Real.ContinuousAt.near;
MetricSpace.Near(x, (y : ℝ) ↦ abs(g(y) - g(x)) < ε / 2)
    by Real.ContinuousAt.near;
for y sufficiently near x: {
  abs((f(y) + g(y)) - (f(x) + g(x)))
     = abs((f(y) - f(x)) + (g(y) - g(x)))
           by substituting
               (ring : (f(y) + g(y)) - (f(x) + g(x))
                   = (f(y) - f(x)) + (g(y) - g(x)))
     ≤ abs(f(y) - f(x)) + abs(g(y) - g(x))
     < ε / 2 + ε / 2
     = ε
}
```

"Near x" here **includes x itself**, so "what holds near x holds at x" needs no
side condition; `MetricSpace.Near.at_centre` is that step. (A punctured
version — 0 < d(x,y) < r, which a limit of a *function* at a point wants — is a
separate notion, not a setting on this one.)

Because the two behave the same way, an argument reasoning at f(y) rather than
at y needs the analogue of `shift`: `MetricSpace.Near.under` carries a
near-fact along a continuous map. This comes up whenever two continuity facts
sit at *different* centres, as in a composition.

## Quick reference

| you want | write |
|---|---|
| to state one | `eventually (m). P(m)` |
| to get one from a hypothesis | `eventually (m). P(m) by <hypothesis>;` |
| to prove one | `for m sufficiently large: { … }` |
| … about points instead | `for y sufficiently near x: { … }` |
| "m is past this index", as an eventually-fact | `Natural.Eventually.beyond` |
| the conclusion doesn't mention m | `done by Natural.Eventually.constant` |
| the conclusion is a contradiction | `done by Natural.Eventually.not_eventually_false` |
| a fact needed at m + offset | `Natural.Eventually.shift` |
| a near-fact needed at f(y) | `MetricSpace.Near.under` |
| what holds near x, at x | `MetricSpace.Near.at_centre` |

## Two things that will look wrong

**"The goal is spelled differently."** The block recognises what it is being
asked to prove by how that is *written*, not by what it unfolds to. If your
statement is an eventually-fact only after unfolding a definition — typically
a membership like `x ∈ Real.eventual_lower_bounds(s)` — write out what it is
and carry on:

```math
change eventually (m). s(N) - q ≤ s(m);
```

**A lemma about eventually-facts won't apply.** For the same reason, a result
whose conclusion is `eventually (m). …` will not discharge a statement you
wrote out longhand as `∃ N. ∀ m ≥ N. …`, even though those are the same
proposition. Write the statement with the `eventually` binder and it matches.
Both of these are known rough edges, not something you are doing wrong.
