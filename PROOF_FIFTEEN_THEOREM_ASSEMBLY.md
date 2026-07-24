# The six final rank-four forms and the Fifteen Theorem assembly

## 0. Scope

This document begins where the rank-four escalation census leaves off.

The existing development has 207 selected positive-definite rank-four escalators:

* 201 are proved universal, conditional on the exact ternary converse interfaces;
* six are nonuniversal and each misses exactly one positive integer;
* four of the six have truant \(15\);
* two have truant \(10\).

The goals here are:

1. prove that each of those six forms represents **every** positive integer other than its truant;
2. deduce that every further escalation of one of the six is universal;
3. state the final ambient-lattice escalation lemma precisely;
4. assemble the critical set

\[
        \{1,2,3,5,6,7,10,14,15\}.
\]

The co-singleton proofs in Sections 3 and 4 are complete relative to the exact ternary converses.  Section 5 is a complete
further-escalation argument.  Section 6 proves the theorem that passes from the enumerated escalation tree to an arbitrary
ambient quadratic form.  The current library does not yet express one feature of the classical definition: an escalation
may be a same-rank integral overlattice.  This document does not pretend that `Matrix.escalation_exists`, which constructs
an abstract rank-\(n+1\) child, is already the ambient theorem.

Every finite calculation in Sections 2--4 is replayed by
[`scripts/check_remaining_converses_and_assembly.js`](scripts/check_remaining_converses_and_assembly.js).

---

## 1. Notation

Let

\[
        g(x,y,z)=x^2+2y^2+2yz+4z^2
\]

be the determinant-\(7\) ternary form used in the final seven covers.

Let

\[
        h(x,y,z)=x^2+2y^2+5z^2.
\]

We use the exact converse

\[
h(\mathbb Z^3)
=
\mathbb Z_{>0}\setminus
\left\{
25^a(25b+10),\ 25^a(25b+15):a,b\ge0
\right\}.                                                     \tag{1.1}
\]

We also use the exact converse

\[
x^2+2y^2+6z^2
\quad\text{represents every positive integer outside}\quad
4^a(8b+5).                                                    \tag{1.2}
\]

Both are proved, relative to their explicit one-class-genus certificates, in
`PROOF_REMAINING_TERNARY_CONVERSES.md`.

For a matrix \(A\), write \(q_A(v)=v^{\mathsf T}Av\).

---

## 2. The six exceptional rank-four forms

Up to integral isometry, the two truant-\(10\) forms are

\[
B_1=
\begin{pmatrix}
1&0&0&0\\
0&2&0&1\\
0&0&3&0\\
0&1&0&4
\end{pmatrix},
\qquad
B_2=
\begin{pmatrix}
1&0&0&0\\
0&2&1&0\\
0&1&4&1\\
0&0&1&5
\end{pmatrix}.                                                \tag{2.1}
\]

The four truant-\(15\) forms are

\[
C_{s,r,c}=
\begin{pmatrix}
1&0&0&0\\
0&2&0&s\\
0&0&5&r\\
0&s&r&c
\end{pmatrix},                                                \tag{2.2}
\]

for

\[
        (s,r,c)\in
        \{(0,0,5),(1,1,5),(1,1,9),(1,2,8)\}.                  \tag{2.3}
\]

Thus

\[
        q_{C_{s,r,c}}(x,y,z,w)
        =x^2+2y^2+5z^2+2syw+2rzw+cw^2.                       \tag{2.4}
\]

These matrices are the six exceptional forms in Bhargava's final table.  The generated library uses different bases for
the two forms in (2.1).  Explicit unimodular changes of basis are:

\[
U_1=
\begin{pmatrix}
1&0&0&0\\
0&-1&-1&0\\
0&0&0&-1\\
0&0&1&0
\end{pmatrix},
\qquad
U_2=
\begin{pmatrix}
1&0&0&0\\
0&-1&-1&-1\\
0&0&1&0\\
0&0&0&-1
\end{pmatrix}.                                                \tag{2.5}
\]

Direct multiplication verifies that \(U_i^{\mathsf T}B_iU_i\) is the corresponding generated library matrix.

The existing finite truant proofs already show:

\[
        B_1,B_2\text{ do not represent }10,
\]

and

\[
        C_{s,r,c}\text{ does not represent }15
\]

for the four triples in (2.3).  What remains is representation of every larger integer.

---

## 3. The two forms that miss \(10\)

### 3.1 The first form

Write

\[
        q_{B_1}(x,y,z,w)
        =x^2+2y^2+3z^2+2yw+4w^2.
\]

The identity

\[
2q_{B_1}(x,y,z,w)
        =(2y+w)^2+2x^2+6z^2+7w^2                            \tag{3.1}
\]

is immediate by expansion.

Put

\[
        U=2y+w.
\]

To represent \(n\) by \(B_1\), it therefore suffices to choose \(w\) so that

\[
        R=2n-7w^2                                             \tag{3.2}
\]

is positive and represented by

\[
        U^2+2x^2+6z^2.                                       \tag{3.3}
\]

There is no parity side condition to check after (3.3): reducing

\[
        R=U^2+2x^2+6z^2=2n-7w^2
\]

modulo \(2\) gives \(U\equiv w\pmod2\), hence \(y=(U-w)/2\) is automatically integral.

If \(2n\) is not of the form \(4^a(8b+5)\), take \(w=0\) and apply (1.2).

It remains to treat

\[
        2n=4^a(8b+5).                                        \tag{3.4}
\]

The right side is even, so \(a\ge1\).  Write \(a=k+1\); then

\[
        n=2\cdot4^k(8b+5).                                   \tag{3.5}
\]

There are three cases.

#### Case 1: \(b\ge1\)

Take \(w=2^{k+1}\).  Then

\[
\begin{aligned}
R
 &=4^{k+1}(8b+5)-7\cdot4^{k+1}\\
 &=4^{k+1}(8b-2)\\
 &=4^k(32b-8).
\end{aligned}
\]

This is positive.  Its primitive \(2\)-adic core has even residue modulo \(8\), not \(5\), so it is not an obstruction
to (1.2).

#### Case 2: \(b=0\) and \(k\ge1\)

Take \(w=2^{k-1}\).  Then

\[
        R=20\cdot4^k-7\cdot4^{k-1}=73\cdot4^{k-1},
\]

whose primitive core is \(73\equiv1\pmod8\).  Again (1.2) applies.

#### Case 3: \(b=0\) and \(k=0\)

Equation (3.5) gives \(n=10\), the known missing integer.

We have proved:

### Theorem 3.1

\[
        q_{B_1}(\mathbb Z^4)=\mathbb Z_{>0}\setminus\{10\}.
\]

The only deep input is the \(q_{126}\) converse (1.2).

---

### 3.2 The second form

Let \(Q_2\) denote the generated-library form

\[
        x^2+2y^2+2yz+4z^2+4yw+7w^2.
\]

Equation (2.5) gives \(Q_2\cong B_2\).  The form \(Q_2\) contains a primitive orthogonal copy of
\(h=\langle1,2,5\rangle\).  In the library basis, one convenient choice of mutually orthogonal vectors is

\[
        a=(-1,0,0,0),\qquad
        b=(0,-1,0,0),\qquad
        c=(0,-1,0,1),
\]

with norms \(1,2,5\).  A vector orthogonal to all three is

\[
        v=(0,-7,10,2),
\]

with norm \(330\).  Therefore \(B_2\) represents every integer of the form

\[
        h(X,Y,Z)+330t^2.                                     \tag{3.6}
\]

If \(n\) is admissible for \(h\), take \(t=0\).  Consider the two primitive exceptional families.

* If \(n=25b+10\) and \(b\ge13\), take \(t=1\).  Then

  \[
        n-330=25(b-13)+5,
  \]

  which is admissible for \(h\).

* If \(n=25b+15\) and \(b\ge53\), take \(t=2\).  Then

  \[
        n-4\cdot330=25(b-53)+20,
  \]

  which is admissible for \(h\).

This leaves the exact finite set

\[
        \{25b+10:0\le b<13\}
        \cup
        \{25b+15:0\le b<53\}.                                \tag{3.7}
\]

An exhaustive bounded calculation shows that every member of (3.7) except \(10\) is represented by \(B_2\).
This is a finite proof certificate, not a heuristic search.  For the largest target in (3.7), positivity gives the bounds

\[
        |x|\le36,\qquad |y|\le56,\qquad |z|\le25,\qquad |w|\le17.
\]

Indeed, in the library basis,

\[
\begin{aligned}
Q_2(x,y,z,w)
={}&x^2+2\left(y+\frac z2+w\right)^2\\
 &+\frac72\left(z-\frac{2w}{7}\right)^2+\frac{33}{7}w^2.      \tag{3.8}
\end{aligned}
\]

The largest target in (3.7) is \(1315\), and (3.8) gives the displayed safe bounds.  For each fixed \(y,z,w\), compute

\[
        R=n-Q_2(0,y,z,w).
\]

There is a representation with those last three coordinates exactly when \(R\) is a nonnegative square.  Exhausting the
displayed integer boxes gives the exact missing set \(\{10\}\) among the 66 targets in (3.7).

The formal artifact should store the resulting witness table and check each equality in the kernel; the enumeration is a
transparent way to produce the certificate, not a new trusted axiom.

It remains to handle square-scaled copies of the exceptional base value \(10\).  The form \(B_2\) represents \(250\), for
example at

\[
        (x,y,z,w)=(0,-1,-2,6)
\]

in the generated-library basis.  Consequently, for \(a\ge1\),

\[
        10\cdot25^a
        =
        q_{B_2}\!\left(5^{a-1}(0,-1,-2,6)\right).
\]

Every other number \(25^a(25b+10)\) or \(25^a(25b+15)\) is obtained by representing its primitive core and scaling all
four coordinates by \(5^a\).

Thus, first for \(Q_2\) and then by the isometry (2.5) for \(B_2\):

### Theorem 3.2

\[
        q_{B_2}(\mathbb Z^4)=\mathbb Z_{>0}\setminus\{10\}.
\]

The only deep input is the \(q_{125}\) converse (1.1); the remaining debt is an explicit finite witness table for (3.7).

---

## 4. The four forms that miss \(15\)

All four proofs use one completion-of-squares calculation.

### Lemma 4.1 (tail correction)

Let \(Q=C_{s,r,c}\).  Choose an integer \(W\) such that

\[
        2\mid sW,\qquad 5\mid rW.
\]

Put

\[
        S=\frac{sW}{2},\qquad T=\frac{rW}{5},
\]

and

\[
        D=cW^2-2S^2-5T^2.                                    \tag{4.1}
\]

Then

\[
        Q(x,y-S,z-T,W)=h(x,y,z)+D.                            \tag{4.2}
\]

Proof.  Substitute and expand:

\[
2(y-S)^2+2s(y-S)W=2y^2-2S^2,
\]

because \(2S=sW\), and similarly

\[
5(z-T)^2+2r(z-T)W=5z^2-5T^2.
\]

The remaining \(W\)-term is (4.1).

Thus, to represent a primitive \(h\)-exception \(n\), it is enough to choose \(W\) for which \(n-D\) is positive and
admissible for \(h\).

### 4.1 Tail data

The following choices work uniformly beyond the displayed cutoff.

\[
\begin{array}{c|c|c|c|c|c|c}
(s,r,c)&\text{exception}&W&S&T&D&\text{new residue}\\ \hline
(0,0,5)&25b+10&1&0&0&5&25b+5\\
(0,0,5)&25b+15&2&0&0&20&25(b-1)+20\\
(1,1,5)&25b+10&10&5&2&430&25(b-17)+5\\
(1,1,5)&25b+15&20&10&4&1720&25(b-69)+20\\
(1,1,9)&25b+10&10&5&2&830&25(b-33)+5\\
(1,1,9)&25b+15&20&10&4&3320&25(b-133)+20\\
(1,2,8)&25b+10&20&10&8&2680&25(b-107)+5\\
(1,2,8)&25b+15&10&5&4&670&25(b-27)+20.
\end{array}                                                   \tag{4.3}
\]

The final column is never in either exceptional residue \(10,15\pmod {25}\).  Therefore (1.1) represents it whenever it
is positive.

The exact finite prefixes not covered by (4.3) are:

\[
\begin{array}{c|c}
(s,r,c)&\text{values to check}\\ \hline
(0,0,5)&25b+15,\quad 0\le b<1,\\
(1,1,5)&25b+10,\ 0\le b<17;\quad25b+15,\ 0\le b<69,\\
(1,1,9)&25b+10,\ 0\le b<33;\quad25b+15,\ 0\le b<133,\\
(1,2,8)&25b+10,\ 0\le b<107;\quad25b+15,\ 0\le b<27.
\end{array}                                                   \tag{4.4}
\]

An exhaustive, positivity-bounded enumeration gives one representing vector for every value in (4.4) except \(15\).
As in Section 3.2, the formal proof artifact must retain the witness table and check the equalities; it need not trust the
enumerator.

For completeness, the bounds used by that enumeration follow from

\[
\begin{aligned}
Q(x,y,z,w)
={}&x^2+2\left(y+\frac{sW}{2}\right)^2
      +5\left(z+\frac{rW}{5}\right)^2\\
 &+\left(c-\frac{s^2}{2}-\frac{r^2}{5}\right)W^2.             \tag{4.5}
\end{aligned}
\]

The coefficient of \(W^2\) is positive in all four cases.  Safe coordinate bounds for the finite sets (4.4) are:

\[
\begin{array}{c|r|rrrr|c}
(s,r,c)&N_{\max}&|x|&|y|&|z|&|w|&
  \text{exact missing set}\\ \hline
(0,0,5)&15&3&3&2&2&\{15\}\\
(1,1,5)&1715&41&40&23&20&\{15\}\\
(1,1,9)&3315&57&51&30&20&\{15\}\\
(1,2,8)&2660&51&47&32&20&\{15\}.
\end{array}                                                   \tag{4.6}
\]

For each target and fixed \(y,z,w\) in the indicated box, the same nonnegative-square test for
\(n-Q(0,y,z,w)\) supplies \(x\).  Thus (4.6) is an independently reproducible finite decision procedure for precisely the
sets in (4.4).

Finally, every form in (2.3) represents \(375=15\cdot25\).  Fixed witnesses are:

\[
\begin{array}{c|c}
(s,r,c)&(x,y,z,w)\\ \hline
(0,0,5)&(0,5,1,8),\\
(1,1,5)&(0,-1,7,4),\\
(1,1,9)&(1,3,-2,6),\\
(1,2,8)&(0,3,5,4).
\end{array}                                                   \tag{4.7}
\]

Hence, for \(a\ge1\), scaling the appropriate vector in (4.7) by \(5^{a-1}\) represents \(15\cdot25^a\).
Every other scaled \(h\)-exception is obtained by representing its primitive core and scaling.

We conclude:

### Theorem 4.2

For every triple in (2.3),

\[
        q_{C_{s,r,c}}(\mathbb Z^4)
        =
        \mathbb Z_{>0}\setminus\{15\}.
\]

Again, the only deep input is (1.1); the remainder is Lemma 4.1 plus the finite witness tables in (4.4).

---

## 5. Every further escalation is universal

### Lemma 5.1

Let \(E\) be an integral positive-definite lattice that represents every positive integer except \(t\).  Let \(L\) be an
integral lattice containing an isometric copy of \(E\) and representing \(t\).  Then \(L\) is universal.

Proof.  If \(n\ne t\), represent \(n\) in the copy of \(E\).  If \(n=t\), use the assumed representation in \(L\).

### Corollary 5.2

Every escalation of one of the six forms in Section 2 is universal, whether its rank stays four or rises to five.

By definition, an escalation of a nonuniversal lattice adjoins a vector of norm equal to its truant.  The leading
rank-four block represents all other positive integers by Theorems 3.1, 3.2, and 4.2; the new vector represents the
truant.  Apply Lemma 5.1.

This argument replaces any enumeration of the roughly 1,630 rank-five children and also handles same-rank integral
overlattices.  No property of any new off-diagonal coefficients is needed.

---

## 6. The ambient escalation lemma

The finite census classifies lattices built by the escalator process.  To deduce a theorem about an arbitrary ambient
lattice \(L\), one needs a containment theorem, not merely the existence of an abstract bordered matrix.

### Theorem 6.1 (ambient escalator containment)

Let \(L\) be a positive-definite integral lattice and let \(T\) be its truant, the least positive integer not represented
by \(L\).  Then \(L\) contains an escalator lattice \(E\) whose truant is \(T\).

Here an escalation of \(E\) is, as in Bhargava's definition, **any** integral lattice

\[
        E'=E+\mathbb Zv
\]

generated by \(E\) and a vector \(v\) whose norm is the truant of \(E\).  Its rank may equal the rank of \(E\) or be one
larger.

Equivalently, one can build inside \(L\) a chain

\[
        0=E_0\subset E_1\subset\cdots\subset E_r=E
\]

such that \(E_{i+1}=E_i+\mathbb Zv_i\), \(q(v_i)\) is the truant of \(E_i\), and the process stops when that truant is
\(T\).

Proof.  Start with \(E_0=0\).  Suppose \(E_i\subset L\) has truant \(t<T\).  By definition of \(T\), the ambient lattice
\(L\) represents \(t\).  Choose \(v_i\in L\) with \(q(v_i)=t\), and put

\[
        E_{i+1}=E_i+\mathbb Zv_i.
\]

This is an escalation inside \(L\).

It remains to show that the process terminates.  A rank increase can occur at most \(\operatorname{rank}(L)\) times.
Suppose instead that \(E_i\subsetneq E_{i+1}\) have the same rank.  Integrality of \(E_{i+1}\) implies

\[
        v_i\in E_i^*
        =
        \{x\in E_i\otimes\mathbb Q:\langle x,E_i\rangle\subseteq\mathbb Z\}.
\]

Thus

\[
        E_i\subsetneq E_{i+1}\subseteq E_i^*.
\]

The quotient \(E_i^*/E_i\) is finite.  Equivalently, the determinants satisfy

\[
        \det(E_{i+1})
        =
        \frac{\det(E_i)}{[E_{i+1}:E_i]^2}
        <
        \det(E_i).                                             \tag{6.1}
\]

Consequently no infinite chain of same-rank steps exists, and the entire construction stops after finitely many steps.
Let its last member be \(E\).

Because \(E\subset L\) and \(L\) does not represent \(T\), neither does \(E\); in particular, the truant of \(E\) is at
most \(T\).  If it were less than \(T\), the construction above would provide another escalation inside \(L\),
contradicting termination.  Its truant is therefore \(T\).

### 6.1 Formalization consequence

The mathematics is complete, but the current library notion `Matrix.IsEscalation(A,B)` fixes \(B\) to have size
\(1+n\) when \(A\) has size \(n\).  It therefore describes only the rank-increasing branch of the classical definition.

The durable API should add a lattice-level relation, for example

```text
IsAmbientEscalation(E, E', L)
```

asserting \(E\subseteq E'\subseteq L\), \(E'=E+\mathbb Zv\), and
\(q(v)=\operatorname{truant}(E)\), without prescribing the rank.  One then needs:

1. the dual-lattice finiteness/determinant descent in (6.1);
2. construction of a maximal finite chain inside \(L\);
3. a bridge showing that the existing finite census includes the same-rank escalators of Bhargava's census, or an
   extension of the internal `IsEscalator` predicate so that it does.

The third item is a representation-of-the-census question, not a missing number-theoretic theorem.

---

## 7. Final assembly

Let

\[
        S=\{1,2,3,5,6,7,10,14,15\}.                           \tag{7.1}
\]

Assume the following completed components.

1. The exact ternary converses in `PROOF_TRIPLE_SQUARES_CONVERSE.md` and
   `PROOF_REMAINING_TERNARY_CONVERSES.md`.
2. The determinant-\(7\) rank-four covers in `PROOF_15_THEOREM_REMAINING.md`.
3. The full Bhargava rank-four census, including escalators reached after same-rank steps:
   201 selected escalators are universal, and the other six are exactly the forms in Section 2.  The generated matrix
   census is intended to certify this list; the formal bridge in Section 6.1 must ensure that its current
   rank-increasing `IsEscalator` predicate has not narrowed the classical list.
4. The co-singleton conclusions of Theorems 3.1, 3.2, and 4.2.
5. The ambient containment theorem, Theorem 6.1.

### Theorem 7.1 (critical truants)

The truant of every nonuniversal positive-definite integral lattice belongs to \(S\).

Proof.  Let \(L\) be nonuniversal, with truant \(T\).  By Theorem 6.1, \(L\) contains an escalator \(E\) with truant
\(T\).

The finite escalation census gives the following alternatives.

* The chain stops before rank four.  Its truant is one of

  \[
        1,2,3,5,6,7,10,14,15;
  \]

  these are precisely the low-rank truants retained by the census.
* It reaches one of the 201 universal rank-four forms, which is impossible because a universal sublattice would make
  \(L\) universal.
* It reaches one of the six exceptional rank-four forms.  Its truant is \(10\) or \(15\).
* It escalates one of those six.  Corollary 5.2 says the resulting lattice is universal, again impossible.

Therefore \(T\in S\).

### Theorem 7.2 (the Fifteen Theorem)

A positive-definite integral quadratic form is universal if and only if it represents

\[
        1,2,3,5,6,7,10,14,15.
\]

Proof.  A universal form plainly represents the nine integers.

Conversely, let \(L\) represent every element of \(S\).  If \(L\) were nonuniversal, Theorem 7.1 would put its truant
\(T\) in \(S\), contradicting the assumption that \(L\) represents every element of \(S\).  Hence \(L\) is universal.

---

## 8. Exact remaining proof debt

After the elementary finite certificates in Sections 3 and 4 are emitted, the theorem rests on the following clearly
delimited items.

\[
\begin{array}{l|l}
\text{item}&\text{nature}\\ \hline
\text{Hasse--Minkowski for ternary spaces}
  &\text{shared classical local-to-global input}\\
\text{four remaining one-class-genus certificates}
  &\text{finite reduction/neighbor computations}\\
\text{determinant-3 one-class certificate}
  &\text{detailed in the triple-squares proof}\\
\text{determinant-7 safe representation theorem}
  &\text{detailed separately in the det-7 proof}\\
\text{ambient escalator containment, Theorem 6.1}
  &\text{elementary proof complete; same-rank API/census bridge still to formalize}\\
\text{rank-four witness/drift certificates}
  &\text{generated finite computations, already patterned in the library}.
\end{array}
\]

The co-singleton argument itself adds no new genus theory.  In particular, no rank-five census is required.

---

## 9. Reviewer checklist

1. Verify identities (3.1) and (4.2) before inspecting any congruence argument.
2. In Section 3.1, check that \(U\equiv w\pmod2\) follows from the representation equation; otherwise the recovery of
   \(y\) would be invalid.
3. Check positivity at every tail subtraction.  The cutoff inequalities in (3.7) and (4.4) are chosen precisely for
   this reason.
4. Check that every exceptional square-scaled family includes its base value.  The fixed \(250\) and \(375\) witnesses
   are what prevent the tail argument from accidentally leaving infinitely many holes.
5. Treat each finite prefix as a witness table to be checked, not merely as a statement that a computer search found no
   counterexample.
6. Do not replace Theorem 6.1 by the existing abstract rank-increasing escalation constructor.  The former is relative
   to an arbitrary ambient lattice and includes same-rank integral overlattices.
7. Verify that Theorem 7.1 uses only containment: a universal sublattice makes the ambient lattice universal, and a
   co-singleton rank-four sublattice plus a vector of its truant makes the resulting over-lattice universal.

---

## 10. References

* M. Bhargava, *On the Conway--Schneeberger Fifteen Theorem*, in
  [*Quadratic Forms and Their Applications*](https://www.maths.ed.ac.uk/~v1ranick/books/dublin.pdf),
  Contemporary Mathematics 272 (2000), 27--37.  This is the source of the escalation definition, the maximal-chain
  ambient argument, the rank-four census, and the six final matrices.
* S. Blackwell, G. Durham, K. Thompson, and T. Treece,
  [*A Generalization of Mordell to Ternary Quadratic Forms*](https://arxiv.org/pdf/1508.02694).  Its Theorem 1(f)
  gives the exact \(x^2+2y^2+5z^2\) represented set, and its introduction explicitly records that the forms treated there
  are alone in their genera.
* B. W. Jones and G. Pall,
  [*Regular and semi-regular positive ternary quadratic forms*](https://archive.ymsc.tsinghua.edu.cn/pacm_download/117/5599-11511_2006_Article_BF02547347.pdf),
  Acta Mathematica 70 (1939), 165--191.  This is a classical source for the separation between local eligibility,
  representation by a genus, and one-class conclusions.

### Reproduction

Run:

```sh
node scripts/check_remaining_converses_and_assembly.js
```

The final line must be:

```text
All remaining-converse and final-assembly finite checks passed.
```
