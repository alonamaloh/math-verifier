# The remaining ternary converse theorems

## 0. Purpose and exact status

This document gives a proof specification for the ternary representation theorems still used as classical interfaces by the
Fifteen Theorem development.  It complements `PROOF_TRIPLE_SQUARES_CONVERSE.md`, which treats

\[
        x^2+y^2+3z^2.
\]

The forms treated here are

\[
\begin{array}{c|c|c}
\text{name} & q(x,y,z) & \text{positive integers not represented}\\ \hline
q_{111} & x^2+y^2+z^2
  & 4^a(8b+7),\\
q_{123} & x^2+2y^2+3z^2
  & 4^a(16b+10),\\
q_{126} & x^2+2y^2+6z^2
  & 4^a(8b+5),\\
q_{136} & x^2+3y^2+6z^2
  & 3b+2\ \text{or}\ 4^a(16b+14),\\
q_{236} & 2x^2+3y^2+6z^2
  & 3b+1\ \text{or}\ 4^a(8b+7),\\
q_{125} & x^2+2y^2+5z^2
  & 25^a(25b+10)\ \text{or}\ 25^a(25b+15).
\end{array}
\]

Here \(a,b\) are arbitrary nonnegative integers.  The first row is Legendre's three-square theorem.  The last five rows are
the exact regular-form converses needed by the current library.

There are two useful simplifications:

* the \(q_{136}\) converse is proved directly from the three-square converse, so it does **not** need an independent genus
  or class-number theorem;
* the three-square converse uses the already formalized Aubry--Davenport--Cassels rational-to-integral descent, so it
  does not need a one-class-genus certificate.

The other four rows are proved by the standard local-to-global argument for a one-class genus.  Accordingly, this proof
specification has two deliberately visible classical inputs:

1. the rational local-to-global theorem for ternary quadratic spaces, in exactly the form stated in
   `PROOF_TRIPLE_SQUARES_CONVERSE.md`, Section 8;
2. a finite certificate that the genera of \(q_{123},q_{126},q_{236},q_{125}\) each contain one integral class.

The second input is not an appeal to the definition of "regular."  It is a finite classification assertion about four
explicit lattices.  A formal development may either check explicit neighbor/reduction certificates for it or temporarily
expose four narrow interfaces.  Nothing below assumes a blanket theorem saying that all forms in a published table are
regular.

All local calculations, including the singular \(2\)-adic cases and the two exceptional \(5\)-adic square classes for
\(q_{125}\), are spelled out below.

Every finite residue calculation in this document is replayed by
[`scripts/check_remaining_converses_and_assembly.js`](scripts/check_remaining_converses_and_assembly.js).
The script has no package dependencies and uses exact integer arithmetic in a range far below JavaScript's exact-integer
limit.

---

## 1. Shared local-to-global engine

Let \(L\) be a positive-definite integral ternary lattice with quadratic form \(q\), and let \(n>0\).

We use the following theorem, proved modulo Hasse--Minkowski in `PROOF_TRIPLE_SQUARES_CONVERSE.md`, Sections 8 and 9.

### Theorem 1.1 (local representation reaches the genus)

If \(n\) is represented by \(L\otimes\mathbb Z_p\) for every prime \(p\), then some integral lattice \(L'\) in the genus of
\(L\) represents \(n\).

The proof has four logically separate parts.

1. The real place is automatic because \(q\) is positive definite and \(n>0\).
2. Hasse--Minkowski gives a rational vector \(v\in L\otimes\mathbb Q\) with \(q(v)=n\).
3. Equal-norm reflections move \(v\) independently into \(L\otimes\mathbb Z_p\) at the finitely many denominator primes.
4. Intersecting the resulting local lattices produces an integral global lattice in the genus of \(L\) that contains \(v\).

No one-class assumption is used in this theorem.

### Corollary 1.2 (one-class genus)

If the genus of \(L\) contains one integral isometry class, then \(L\) represents every positive integer represented by
\(L\otimes\mathbb Z_p\) for all \(p\).

Indeed, Theorem 1.1 supplies \(L'\) in the genus representing \(n\), and the one-class hypothesis supplies an integral
isometry \(L'\cong L\).

Thus the remaining work is exact local analysis plus four finite class-number certificates.  Three squares uses the
already formalized Aubry--Davenport--Cassels rational-to-integral descent instead.

---

## 2. Elementary local tools

### Lemma 2.1 (odd-prime square lifting)

Let \(p\) be odd and let \(u\in\mathbb Z_p^\times\).  If the reduction of \(u\) modulo \(p\) is a square, then \(u\) is a
square in \(\mathbb Z_p^\times\).

This is ordinary Hensel lifting applied to \(X^2-u\): a nonzero root modulo \(p\) has derivative \(2X\), a unit modulo
\(p\).

### Lemma 2.2 (binary universality at an odd prime)

If \(-d\) is a square in \(\mathbb Z_p^\times\), then

\[
        X^2+dY^2
\]

represents every element of \(\mathbb Z_p\).

Choose \(\delta^2=-d\).  Since \(2\) and \(\delta\) are units,

\[
 X^2+dY^2=(X+\delta Y)(X-\delta Y),
\]

and for any \(m\in\mathbb Z_p\) one may solve

\[
 X+\delta Y=m,\qquad X-\delta Y=1.
\]

### Lemma 2.3 (good odd primes)

Let \(q\) be a nondegenerate integral ternary form and let \(p\nmid 2\det(q)\).  Then every element of \(\mathbb Z_p\) is
represented by \(q\).

For a unit target, reduce modulo \(p\).  A nondegenerate ternary quadratic form over \(\mathbb F_p\) represents every
element: after diagonalization, the two sets

\[
        \{aX^2+bY^2:X,Y\in\mathbb F_p\}
        \quad\text{and}\quad
        \{t-cZ^2:Z\in\mathbb F_p\}
\]

have cardinalities whose sum exceeds \(p\), so they intersect.  A representing vector for a nonzero target is
nonsingular, hence lifts.

For a target divisible by \(p\), first choose a nonzero isotropic vector modulo \(p\).  It is nonsingular because the form
is nondegenerate.  Hensel lifting with the desired \(p\)-adic target then gives an exact representation.

### Lemma 2.4 (singular \(2\)-adic lifting)

Let \(f\in\mathbb Z_2[X_1,\ldots,X_m]\).  Suppose

\[
        f(a)\equiv n\pmod {2^N}
\]

and, for some \(i\),

\[
        v_2\!\left(\frac{\partial f}{\partial X_i}(a)\right)=s,
        \qquad N>2s.
\]

Then \(a\) lifts to a solution of \(f(x)=n\) in \(\mathbb Z_2^m\).

This is the usual strong form of Hensel's lemma.  In every table below \(N=5\) and \(s\le2\), so the displayed solutions
modulo \(32\) lift.

### Lemma 2.5 (scaling)

For every diagonal ternary form in this document,

\[
        q(2^a x,2^a y,2^a z)=4^a q(x,y,z),
\]

and

\[
        q(5^a x,5^a y,5^a z)=25^a q(x,y,z).
\]

Consequently, after proving an exact criterion for a primitive \(2\)-adic or \(5\)-adic core, the stated infinite
exceptional square classes follow.

---

## 3. The exact \(2\)-adic calculations

The following table records the primitive obstruction for each form.

\[
\begin{array}{c|c}
q & \text{primitive residues not represented in }\mathbb Z_2\\ \hline
q_{111} & 7\pmod 8,\\
q_{123} & 10\pmod {16},\\
q_{126} & 5\pmod 8,\\
q_{136} & 14\pmod {16},\\
q_{236} & 7\pmod 8,\\
q_{125} & \text{none}.
\end{array}
\]

Here "primitive" means that the target is not divisible by \(4\).

### 3.1 Necessity and descent

For \(q_{111}\), if

\[
        x^2+y^2+z^2\equiv0\pmod4,
\]

then \(x,y,z\) are all even.  Dividing by \(4\) repeatedly reduces to a primitive target.  Squares modulo \(8\) are
\(0,1,4\), and three such squares cannot sum to \(7\pmod8\).

The other four \(2\)-adically obstructed forms use the elementary identity

\[
        r^2+3s^2
        =
        \left(\frac{r+3s}{2}\right)^2
        3\left(\frac{r-s}{2}\right)^2                         \tag{3.1}
\]

whenever \(r\equiv s\pmod2\).  If \(r,s\) are odd, change the sign of \(s\), if necessary, so that
\(r\equiv s\pmod4\).  Then both new coordinates in (3.1) are even.

This gives the following descent statements.

* If \(q_{123}(x,y,z)\) is divisible by \(4\), parity forces either all coordinates even or \(x,z\) odd and \(y\) even.
  In the second case apply (3.1) to \(x^2+3z^2\).  The represented target divided by \(4\) is represented again by
  \(q_{123}\).
* If \(q_{126}(x,y,z)\) is divisible by \(4\), the nontrivial parity case is \(y,z\) odd and \(x\) even.  Apply (3.1)
  to \(y^2+3z^2\), remembering the common coefficient \(2\).
* If \(q_{136}(x,y,z)\) is divisible by \(4\), apply (3.1) to \(x^2+3y^2\).
* If \(q_{236}(x,y,z)\) is divisible by \(4\), apply (3.1) to \(x^2+3z^2\), remembering the common coefficient \(2\).

In each case, repeated descent reduces to a target not divisible by \(4\).  Direct calculation modulo \(16\) gives,
respectively,

\[
        10;\qquad 5,13;\qquad 14;\qquad 7,15
\]

as the missing primitive residues.  Scaling back gives exactly the four infinite \(2\)-adic obstruction families in the
statement.

### 3.2 Sufficiency

For auditability, the next table gives a solution modulo \(32\) for every allowed primitive residue.  An entry

\[
        r:(x,y,z)
\]

means \(q(x,y,z)\equiv r\pmod {32}\).  Every displayed triple has at least one partial derivative with \(2\)-adic valuation
at most \(2\), so Lemma 2.4 applies.

\[
\begin{array}{c|l}
q_{111}
&
\begin{array}{l}
1:(0,0,1),\ 2:(0,1,1),\ 3:(1,1,1),\ 5:(0,1,2),\ 6:(1,1,2),\\
9:(0,0,3),\ 10:(0,1,3),\ 11:(1,1,3),\ 13:(0,2,3),\ 14:(1,2,3),\\
17:(0,1,4),\ 18:(0,3,3),\ 19:(1,3,3),\ 21:(1,2,4),\ 22:(2,3,3),\\
25:(0,0,5),\ 26:(0,1,5),\ 27:(1,1,5),\ 29:(0,2,5),\ 30:(1,2,5)
\end{array}\\[6pt]
q_{123}
&
\begin{array}{l}
1:(1,0,0),\ 2:(0,1,0),\ 3:(0,0,1),\ 5:(0,1,1),\ 6:(1,1,1),\\
7:(2,0,1),\ 9:(1,2,0),\ 11:(0,0,5),\ 13:(0,1,5),\ 14:(0,1,2),\\
15:(1,1,2),\ 17:(1,0,4),\ 18:(0,1,4),\ 19:(0,0,7),\ 21:(0,1,7),\\
22:(1,1,7),\ 23:(2,0,7),\ 25:(1,2,4),\ 27:(0,0,3),\ 29:(0,1,3),\\
30:(0,3,2),\ 31:(1,3,2)
\end{array}\\[6pt]
q_{126}
&
\begin{array}{l}
1:(1,0,0),\ 2:(0,1,0),\ 3:(1,1,0),\ 6:(0,0,1),\ 7:(1,0,1),\\
9:(1,1,1),\ 10:(0,3,2),\ 11:(1,3,2),\ 14:(0,2,1),\ 15:(1,2,1),\\
17:(3,1,1),\ 18:(0,3,0),\ 19:(1,3,0),\ 22:(0,0,3),\ 23:(1,0,3),\\
25:(1,0,2),\ 26:(0,1,2),\ 27:(1,1,2),\ 30:(0,2,3),\ 31:(1,2,3)
\end{array}
\end{array}
\]

For \(q_{136}\), the allowed primitive residues and witnesses are

\[
\begin{array}{l}
1:(1,0,0),\ 2:(1,3,1),\ 3:(0,1,0),\ 5:(1,2,2),\ 6:(0,0,1),\
7:(1,0,1),\\
9:(0,1,1),\ 10:(1,1,1),\ 11:(0,5,0),\ 13:(1,2,0),\ 15:(3,0,1),\\
17:(1,4,0),\ 18:(3,1,1),\ 19:(1,2,1),\ 21:(3,2,0),\ 22:(0,0,3),\
23:(1,0,3),\\
25:(1,0,2),\ 26:(1,1,3),\ 27:(0,1,2),\ 29:(2,1,3),\ 31:(2,1,2).
\end{array}
\]

For \(q_{236}\), the allowed primitive residues and witnesses are

\[
\begin{array}{l}
1:(0,3,1),\ 2:(1,0,0),\ 3:(0,1,0),\ 5:(1,1,0),\ 6:(0,0,1),\
9:(0,1,1),\\
10:(3,0,2),\ 11:(1,1,1),\ 13:(3,1,2),\ 14:(1,2,0),\
17:(2,1,1),\ 18:(0,2,1),\\
19:(0,3,2),\ 21:(3,1,0),\ 22:(0,0,3),\ 25:(0,1,3),\
26:(1,0,2),\\
27:(0,1,2),\ 29:(1,1,2),\ 30:(2,0,3).
\end{array}
\]

Finally, \(q_{125}\) has no \(2\)-adic obstruction.  The following table covers all residues modulo \(32\):

\[
\begin{array}{rrrr}
0:(1,1,5)&1:(1,0,0)&2:(0,1,0)&3:(1,1,0)\\
4:(2,0,0)&5:(0,0,1)&6:(0,3,2)&7:(0,1,1)\\
8:(1,1,1)&9:(1,2,0)&10:(2,3,2)&11:(2,1,1)\\
12:(2,2,0)&13:(0,0,3)&14:(1,0,3)&15:(0,1,3)\\
16:(1,1,3)&17:(1,0,4)&18:(0,1,4)&19:(1,1,4)\\
20:(0,0,2)&21:(0,0,7)&22:(0,1,2)&23:(0,1,7)\\
24:(1,1,7)&25:(1,2,4)&26:(2,1,2)&27:(2,1,7)\\
28:(0,2,2)&29:(0,0,5)&30:(1,0,5)&31:(0,1,5).
\end{array}
\]

These finite tables are proof certificates, not empirical evidence: each entry is an equality in \(\mathbb Z/32\mathbb Z\), and
Lemma 2.4 turns it into an exact \(2\)-adic representation.

---

## 4. Odd bad primes

Only \(3\) and \(5\) require separate treatment.

### 4.1 The prime \(3\) for \(q_{123}\) and \(q_{126}\)

Both forms contain the binary subform

\[
        x^2+2y^2.
\]

Since \(-2\equiv1\pmod3\), Lemmas 2.1 and 2.2 show that this binary form represents every element of \(\mathbb Z_3\).
Thus \(q_{123}\) and \(q_{126}\) have no \(3\)-adic obstruction.

### 4.2 The prime \(3\) for \(q_{136}\)

Modulo \(3\),

\[
        q_{136}(x,y,z)\equiv x^2.
\]

Therefore a represented \(3\)-adic unit must be \(0\) or \(1\) modulo \(3\); equivalently, an integer congruent to \(2\)
modulo \(3\) is not represented.

Conversely:

* if \(n\in\mathbb Z_3^\times\) and \(n\equiv1\pmod3\), then \(n\) is a square in \(\mathbb Z_3\), so take \(y=z=0\);
* if \(3\mid n\), set \(x=0\) and divide the equation by \(3\).  It remains to represent \(n/3\) by
  \(y^2+2z^2\), which is universal over \(\mathbb Z_3\) by Lemma 2.2.

Thus the exact \(3\)-adic obstruction is \(n\equiv2\pmod3\).

### 4.3 The prime \(3\) for \(q_{236}\)

Modulo \(3\),

\[
        q_{236}(x,y,z)\equiv2x^2.
\]

The possible residues are \(0\) and \(2\), so \(n\equiv1\pmod3\) is impossible.

Conversely:

* if \(n\in\mathbb Z_3^\times\) and \(n\equiv2\pmod3\), then \(n/2\equiv1\pmod3\) is a square in
  \(\mathbb Z_3\), so take \(y=z=0\);
* if \(3\mid n\), set \(x=0\), divide by \(3\), and again use universality of \(y^2+2z^2\).

Thus the exact \(3\)-adic obstruction is \(n\equiv1\pmod3\).

### 4.4 The prime \(5\) for \(q_{125}\)

Modulo \(5\),

\[
        q_{125}(x,y,z)\equiv x^2+2y^2.
\]

Because \(-2\) is not a square modulo \(5\), the congruence

\[
        x^2+2y^2\equiv0\pmod5
\]

forces \(x\equiv y\equiv0\pmod5\).

Write \(n=25^a m\), where \(25\nmid m\).  Scaling reduces the problem to \(m\).

If \(5\nmid m\), the binary form \(x^2+2y^2\) represents \(m\) modulo \(5\): its nonzero values are all four unit
classes.  At least one of \(x,y\) is nonzero, so the solution lifts nonsingularly.

Suppose \(v_5(m)=1\), so \(m=5u\) with \(u\in\mathbb Z_5^\times\).  Any representation forces \(5\mid x,y\).  Reducing
the equation modulo \(25\) gives

\[
        5z^2\equiv5u\pmod {25},
\]

hence

\[
        z^2\equiv u\pmod5.                                    \tag{4.1}
\]

Thus \(u\equiv1\) or \(4\pmod5\) is necessary.  It is also sufficient: lift a square root \(z^2=u\) in
\(\mathbb Z_5^\times\) and take \(x=y=0\).

The excluded unit classes \(u\equiv2,3\pmod5\) give

\[
        m\equiv10,15\pmod {25}.
\]

Restoring the factor \(25^a\), the exact \(5\)-adic exceptions are

\[
        25^a(25b+10),\qquad 25^a(25b+15).
\]

There are no other bad odd primes for \(q_{125}\).

---

## 5. Three squares and the four one-class-genus converses

We now state the finite classification input exactly.

### Classical Input C1 (four explicit one-class genera)

Each of the following integral lattices is the only integral isometry class in its genus:

\[
        \langle1,2,3\rangle,\quad
        \langle1,2,6\rangle,\quad
        \langle2,3,6\rangle,\quad
        \langle1,2,5\rangle.                                  \tag{C1}
\]

This is the only class-number input in this document.

For a kernel-checkable treatment, (C1) should be replaced by one of the following finite certificate packages.

1. Enumerate reduced positive ternary forms at the relevant determinant, assign each to a genus by explicit local
   isometries, and exhibit a unimodular isometry from the unique member of the desired genus to the displayed diagonal
   form.
2. Enumerate the \(p\)-neighbor graph at primes dividing \(2\det(q)\), prove that the component is the whole genus, and
   show that the component contains one vertex.

The first method is closest to the determinant-\(3\) proof already written for \(q_{113}\).  The second is likely more
reusable for the determinant-\(7\) work.  A citation may stand temporarily at this boundary, but it must have exactly the
four instances in (C1); the phrase "the form is regular" is too strong and too opaque to serve as an interface.

### Rational-to-integral three-square descent

Suppose \(n\) is represented rationally by three squares.  Clearing denominators gives

\[
        a^2+b^2+c^2=nd^2,\qquad d\ge1.                        \tag{5.1}
\]

We prove by strong induction on \(d\) that \(n\) is represented integrally.  Divide with balanced remainders:

\[
\begin{aligned}
a&=dq_x+r_x,&4r_x^2&\le d^2,\\
b&=dq_y+r_y,&4r_y^2&\le d^2,\\
c&=dq_z+r_z,&4r_z^2&\le d^2.
\end{aligned}                                                 \tag{5.2}
\]

Put

\[
\begin{aligned}
R&=r_x^2+r_y^2+r_z^2,\\
C&=q_x^2+q_y^2+q_z^2-n,\\
D&=q_xr_x+q_yr_y+q_zr_z,\\
s&=-2D-dC.
\end{aligned}
\]

Expanding (5.1) through (5.2) gives

\[
        R=ds.                                                  \tag{5.3}
\]

If \(R=0\), all three remainders vanish.  Cancelling \(d^2\) in (5.1) gives

\[
        q_x^2+q_y^2+q_z^2=n,
\]

and the descent is finished.

If \(R>0\), the balanced bounds give

\[
        0<R\le\frac34d^2<d^2.
\]

Together with (5.3), this gives \(0<s<d\).  Define

\[
\begin{aligned}
a'&=sq_x+Cr_x,\\
b'&=sq_y+Cr_y,\\
c'&=sq_z+Cr_z.
\end{aligned}
\]

Using \(R=ds\) and \(s+2D+dC=0\), direct expansion gives

\[
        (a')^2+(b')^2+(c')^2=ns^2.                            \tag{5.4}
\]

Equation (5.4) is a scaled representation with strictly smaller positive denominator \(s\), so the induction hypothesis
finishes.  This is the Aubry--Davenport--Cassels descent already implemented in
`Algebra/three_squares_rational_descent`.

### Theorem 5.1 (three squares)

For \(n>0\),

\[
        n=x^2+y^2+z^2
\]

for some integers \(x,y,z\) if and only if \(n\ne4^a(8b+7)\).

Necessity is Section 3.1.  For sufficiency, Section 3.2 gives a \(\mathbb Z_2\)-representation; Lemma 2.3 gives a
\(\mathbb Z_p\)-representation at every odd prime.  Apply Hasse--Minkowski to

\[
        X^2+Y^2+Z^2-nT^2.
\]

It gives a nonzero rational zero.  Positivity forces \(T\ne0\), so division by \(T\) gives a rational three-square
representation of \(n\).  The descent above makes it integral.

### Theorem 5.2 (the \(1,2,3\) converse)

For \(n>0\),

\[
        n=x^2+2y^2+3z^2
\]

if and only if \(n\ne4^a(16b+10)\).

Necessity and the exact \(2\)-adic sufficiency are in Section 3.  There is no \(3\)-adic obstruction by Section 4.1, and
all other odd primes are covered by Lemma 2.3.  Apply Theorem 1.1 and the \(\langle1,2,3\rangle\) instance of (C1).

### Theorem 5.3 (the \(1,2,6\) converse)

For \(n>0\),

\[
        n=x^2+2y^2+6z^2
\]

if and only if \(n\ne4^a(8b+5)\).

The proof is identical in structure to Theorem 5.2, using the \(q_{126}\) row of Section 3 and the
\(\langle1,2,6\rangle\) instance of (C1).

### Theorem 5.4 (the \(2,3,6\) local converse)

For \(n>0\),

\[
        n=2x^2+3y^2+6z^2
\]

if and only if

\[
        n\not\equiv1\pmod3
        \quad\text{and}\quad
        n\ne4^a(8b+7).
\]

Necessity follows from reduction modulo \(3\) and the \(2\)-adic descent in Section 3.  Sufficiency follows from
Sections 3 and 4.3 at the bad primes and Lemma 2.3 elsewhere, followed by Theorem 1.1 and the
\(\langle2,3,6\rangle\) instance of (C1).

The library phrases the first condition by supplying a witness \(w\) with

\[
        n\equiv2w^2\pmod3.
\]

These formulations are equivalent: the values of \(2w^2\) modulo \(3\) are exactly \(0\) and \(2\).

### Theorem 5.5 (the \(1,2,5\) converse)

For \(n>0\),

\[
        n=x^2+2y^2+5z^2
\]

if and only if

\[
        n\ne25^a(25b+10)
        \quad\text{and}\quad
        n\ne25^a(25b+15).
\]

Section 3 proves that there is no \(2\)-adic obstruction.  Section 4.4 proves that the displayed families are the exact
\(5\)-adic obstructions.  Lemma 2.3 handles all other odd primes.  Theorem 1.1 and the
\(\langle1,2,5\rangle\) instance of (C1) finish the proof.

---

## 6. The \(1,3,6\) converse without a new genus input

This converse follows from Theorem 5.1 by two elementary changes of variables.

### Lemma 6.1

For \(n>0\),

\[
        n=X^2+U^2+2V^2
\]

if and only if \(2n\) is a sum of three squares.

One direction is the identity

\[
        2(X^2+U^2+2V^2)
        =(X+U)^2+(X-U)^2+(2V)^2.
\]

Conversely, suppose

\[
        2n=A^2+B^2+C^2.
\]

The sum is even, so either all three coordinates are even or exactly two are odd.  After permuting, arrange
\(A\equiv B\pmod2\) and \(C\) even.  Then

\[
        X=\frac{A+B}{2},\qquad
        U=\frac{A-B}{2},\qquad
        V=\frac C2
\]

are integers and satisfy \(n=X^2+U^2+2V^2\).

### Lemma 6.2

For integers \(x,y,z\), put

\[
        U=y+2z,\qquad V=y-z.
\]

Then

\[
        x^2+3y^2+6z^2=x^2+U^2+2V^2.                           \tag{6.1}
\]

Conversely, \(U,V\) arise from integer \(y,z\) precisely when

\[
        U\equiv V\pmod3,
\]

in which case

\[
        y=\frac{U+2V}{3},\qquad z=\frac{U-V}{3}.               \tag{6.2}
\]

### Lemma 6.3 (arranging the congruence)

Suppose

\[
        n=X^2+U^2+2V^2
\]

and \(n\) is a square modulo \(3\).  By interchanging \(X\) and \(U\) and changing the sign of the chosen coordinate, one
may arrange

\[
        U\equiv V\pmod3.
\]

Proof.  Squares modulo \(3\) are \(0,1\).

If \(V\equiv0\), then \(n\equiv X^2+U^2\).  For \(n\equiv0\), both \(X,U\) vanish modulo \(3\), so either choice works.
For \(n\equiv1\), exactly one of \(X,U\) vanishes; call that coordinate \(U\).

If \(V\not\equiv0\), then \(2V^2\equiv2\).  For \(n\equiv0\), exactly one of \(X,U\) is nonzero; choose it as \(U\) and
change its sign to match \(V\).  For \(n\equiv1\), both \(X,U\) are nonzero; choose either and change its sign to match
\(V\).  This exhausts the cases.

### Lemma 6.4 (obstruction conversion)

\[
        2n=4^a(8b+7)
\]

for some \(a,b\ge0\) if and only if

\[
        n=4^c(16d+14)
\]

for some \(c,d\ge0\).

The forward equation has even left side, so \(a\ge1\), and division by \(2\) gives

\[
        n=2\cdot4^{a-1}(8b+7)=4^{a-1}(16b+14).
\]

The reverse implication is obtained by multiplying by \(2\).

### Theorem 6.5 (the \(1,3,6\) local converse)

Let \(n>0\).  Suppose

1. \(n\) is a square modulo \(3\), and
2. \(n\ne4^a(16b+14)\) for all \(a,b\ge0\).

Then

\[
        n=x^2+3y^2+6z^2
\]

for some integers \(x,y,z\).

By Lemma 6.4, \(2n\) is not obstructed in the three-square theorem.  Theorem 5.1 and Lemma 6.1 give

\[
        n=X^2+U^2+2V^2.
\]

Lemma 6.3 arranges \(U\equiv V\pmod3\).  Define \(y,z\) by (6.2), and use (6.1).

This proves the exact interface `Matrix.OneThreeSixLocalConverse` from `Matrix.ThreeSquaresConverse`; it should not
remain an independent classical axiom.

---

## 7. An optional direct route for \(q_{236}\)

There is a useful identity

\[
        2x^2+3y^2+6z^2
        =(x+y+z)^2+(x-y-z)^2+(y-2z)^2.                        \tag{7.1}
\]

Its inverse requires two simultaneous congruences:

\[
        A\equiv B\pmod2,
        \qquad
        \frac{A-B}{2}\equiv C\pmod3.
\]

The local hypotheses in Theorem 5.4 are exactly what one expects to make such a coordinate arrangement possible, but a
complete permutation-and-sign argument has not been written here.  Until it is, (7.1) is only a promising way to remove
the \(\langle2,3,6\rangle\) class-number input; it is not part of the proof.

This distinction matters.  Theorem 5.4 is complete relative to (C1); it is not presently reduced to the three-square
theorem.

---

## 8. Formalization dependency ledger

The following table separates elementary work from genuine classical debt.

\[
\begin{array}{l|l|l}
\text{result} & \text{new dependency} & \text{status of human proof}\\ \hline
q_{111}\text{ converse}
  & \text{Hasse--Minkowski}
  & \text{exact local proof and integral descent complete}\\
q_{123}\text{ converse}
  & \text{Hasse--Minkowski}+\operatorname{classno}(q_{123})=1
  & \text{exact local proof complete}\\
q_{126}\text{ converse}
  & \text{Hasse--Minkowski}+\operatorname{classno}(q_{126})=1
  & \text{exact local proof complete}\\
q_{236}\text{ converse}
  & \text{Hasse--Minkowski}+\operatorname{classno}(q_{236})=1
  & \text{exact local proof complete}\\
q_{125}\text{ converse}
  & \text{Hasse--Minkowski}+\operatorname{classno}(q_{125})=1
  & \text{exact local proof complete}\\
q_{136}\text{ converse}
  & q_{111}\text{ converse only}
  & \text{complete direct reduction}.
\end{array}
\]

The \(q_{113}\) converse is handled separately in `PROOF_TRIPLE_SQUARES_CONVERSE.md`; there the determinant-\(3\)
one-class calculation is already expanded rather than included in (C1).

### Recommended formalization order

1. Formalize Lemmas 2.1--2.5 and the finite residue-certificate checker.
2. Derive `OneThreeSixLocalConverse` immediately from `ThreeSquaresConverse`.
3. Implement the shared local-to-genus theorem once.
4. Choose a certificate representation for one-class genera and test it first on \(\langle1,2,3\rangle\).
5. Check the other three instances of (C1).
6. Replace the four classical interfaces by the resulting theorems.

The finite residue tables should be generated from a tiny auditable program but checked in the proof kernel as explicit modular
equalities.  The generator is convenience; the table plus the lifting lemma is the proof.

---

## 9. Reviewer checklist

A reviewer should check the following points in particular.

1. The strong \(2\)-adic Hensel inequality is \(N>2s\), and every modular witness has \(s\le2\).
2. The descent identity (3.1) is applied only after the sign has been chosen so both new coordinates are even.
3. The \(5\)-adic proof for \(q_{125}\) uses anisotropy of \(x^2+2y^2\) modulo \(5\); without it, (4.1) does not follow.
4. The \(q_{136}\) coordinate selection treats all four combinations of \(n\bmod3\) and \(V\bmod3\).
5. No direct proof of the \(q_{236}\) converse is inferred merely from identity (7.1).
6. The one-class assertion (C1) is exactly four finite claims, not a hidden general regularity theorem.
7. The local-to-genus theorem is not confused with local-to-the-original-lattice; the one-class certificate is what closes
   that final step.

---

## 10. References

* B. W. Jones and G. Pall,
  [*Regular and semi-regular positive ternary quadratic forms*](https://archive.ymsc.tsinghua.edu.cn/pacm_download/117/5599-11511_2006_Article_BF02547347.pdf),
  Acta Mathematica 70 (1939), 165--191.
* W. C. Jagy, I. Kaplansky, and A. Schiemann,
  [*There are 913 regular ternary forms*](https://www.cambridge.org/core/services/aop-cambridge-core/content/view/EA55EE9BAFC8AC68178F12FD4DF06CAA/S002557930001264Xa.pdf/there_are_913_regular_ternary_forms.pdf),
  Mathematika 44 (1997), 332--341.
* S. Blackwell, G. Durham, K. Thompson, and T. Treece,
  [*A Generalization of Mordell to Ternary Quadratic Forms*](https://arxiv.org/pdf/1508.02694).  Its Theorem 1 gives the
  exact represented sets of the Ramanujan--Dickson diagonal ternaries used here; its introduction states that the forms
  treated in the paper are alone in their genera.
* P. Doyle, J. Muskat, A. Pehlivan, and K. S. Williams,
  [*Positive integers represented by regular ternary quadratic forms*](https://math.colgate.edu/~integers/t45/t45.pdf),
  Integers 19 (2019), Paper A45.  Its tables are a useful independent statement check for every exceptional family in
  Section 0.

### Reproduction

Run:

```sh
node scripts/check_remaining_converses_and_assembly.js
```

The final line must be:

```text
All remaining-converse and final-assembly finite checks passed.
```
