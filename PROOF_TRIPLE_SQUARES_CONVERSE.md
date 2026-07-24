# A complete proof specification for \(x^2+y^2+3z^2\)

## 1. Purpose and status

This document proves the exact statement needed by
`Matrix.TripleSquaresConverse`:

> For every \(n\in\mathbb N\), if
> \[
>   n\ne 9^a(9b+6)
>   \qquad(a,b\in\mathbb N),
> \]
> then there are \(x,y,z\in\mathbb Z\) such that
> \[
>   n=x^2+y^2+3z^2.
> \]

It also proves the converse obstruction, and therefore the exact
characterization

\[
 n=x^2+y^2+3z^2
 \quad\Longleftrightarrow\quad
 n\notin\{9^a(9b+6):a,b\ge0\}.
\]

The proof is written as a formalization specification. Every elementary
ingredient is proved below. One substantial classical theorem is used:
Hasse--Minkowski for rational quadratic forms. Its exact statement and exact
point of use are isolated in Section 8. No theorem saying that this
particular ternary form is regular, or that its genus has one class, is
assumed. The one-class calculation is proved directly in Sections 10--14.

The argument has four parts.

1. Compute the integral local representation conditions. All primes except
   \(3\) are automatic; at \(3\), the single missing square class is exactly
   \(9^a(9b+6)\).
2. Prove that everywhere-local integral representation gives representation
   by some integral lattice in the genus.
3. Prove directly that the genus of
   \(\langle1,1,3\rangle\) has one integral class.
4. Assemble the result.

This proof is independent of Legendre's three-squares converse.

## 2. Conventions

Let \(V=\mathbb Q^3\) and

\[
  q(x,y,z)=x^2+y^2+3z^2.
\]

Let \(B\) be the symmetric bilinear form with
\[
 B((x,y,z),(x',y',z'))=xx'+yy'+3zz',
 \qquad q(v)=B(v,v).
\]

Let
\[
  L=\mathbb Z^3,\qquad
  \operatorname{Gram}(L)=
  \begin{pmatrix}
  1&0&0\\
  0&1&0\\
  0&0&3
  \end{pmatrix}.
\]

An **integral lattice** \(M\) in a rational quadratic space is a free
\(\mathbb Z\)-module of full rank such that \(B(M,M)\subseteq\mathbb Z\).
Its determinant is the determinant of a Gram matrix in any integral basis.
Changing basis by \(\operatorname{GL}_r(\mathbb Z)\) does not change it.

For a prime \(p\), write
\[
 M_p=M\otimes_{\mathbb Z}\mathbb Z_p,\qquad
 V_p=V\otimes_{\mathbb Q}\mathbb Q_p.
\]
Two positive integral lattices are in the same **genus** when they are
isometric over \(\mathbb R\) and over \(\mathbb Z_p\) for every prime \(p\).

A vector in a \(\mathbb Z_p\)-lattice is **primitive** when it does not
belong to \(pM_p\). A \(\mathbb Z_p\)-isometry preserves primitivity.

Our Gram-matrix convention is important. A binary Gram matrix
\[
 \begin{pmatrix}a&b\\b&c\end{pmatrix}
\]
has quadratic polynomial \(ax^2+2bxy+cy^2\) and determinant \(ac-b^2\).

## 3. Two lifting lemmas

### Lemma 3.1: simple-root Hensel lifting

Let \(p\) be a prime, \(f(T)\in\mathbb Z_p[T]\), and \(t_1\in\mathbb Z_p\).
If
\[
 f(t_1)\equiv0\pmod p,\qquad f'(t_1)\not\equiv0\pmod p,
\]
then there is \(t\in\mathbb Z_p\) such that
\[
 t\equiv t_1\pmod p,\qquad f(t)=0.
\]

#### Proof

Suppose inductively that \(f(t_k)\equiv0\pmod {p^k}\). Write
\[
 f(t_k)=p^k e_k.
\]
Seek \(t_{k+1}=t_k+p^k s_k\), with \(s_k\) chosen modulo \(p\). Taylor
expansion gives
\[
 f(t_k+p^k s_k)
 \equiv f(t_k)+p^k s_k f'(t_k)
 \pmod {p^{k+1}}.
\]
Because \(f'(t_k)\equiv f'(t_1)\not\equiv0\pmod p\), there is a unique
\(s_k\pmod p\) satisfying
\[
 e_k+s_kf'(t_k)\equiv0\pmod p.
\]
Thus \(f(t_{k+1})\equiv0\pmod {p^{k+1}}\). The sequence is Cauchy and
converges in the complete ring \(\mathbb Z_p\) to the required root. \(\square\)

### Corollary 3.2: odd-prime unit squares

For odd \(p\), if a unit \(u\in\mathbb Z_p^\times\) is a nonzero square
modulo \(p\), then \(u\) is a square in \(\mathbb Z_p^\times\).

#### Proof

Choose \(t_1\not\equiv0\pmod p\) with \(t_1^2\equiv u\pmod p\) and apply
Lemma 3.1 to \(f(T)=T^2-u\). Its derivative \(2t_1\) is a unit. \(\square\)

### Lemma 3.3: 2-adic unit squares

If \(u\in\mathbb Z_2^\times\) and \(u\equiv1\pmod8\), then \(u\) is a
square in \(\mathbb Z_2^\times\).

#### Proof

Start with the odd approximation \(t_3=1\), for which
\(t_3^2\equiv u\pmod8\). Suppose \(t_k\) is odd and
\(t_k^2\equiv u\pmod {2^k}\), with \(k\ge3\). The two choices
\[
 t_k,\qquad t_k+2^{k-1}
\]
have squares differing by
\[
 2^k t_k+2^{2k-2}\equiv2^k\pmod {2^{k+1}}.
\]
Consequently exactly one of them has square congruent to \(u\) modulo
\(2^{k+1}\). Choose it as \(t_{k+1}\).

The differences \(t_{k+1}-t_k\) are divisible by \(2^{k-1}\), so the
sequence is Cauchy. Its limit \(t\in\mathbb Z_2^\times\) satisfies
\(t^2=u\). \(\square\)

## 4. The good primes \(p\ne2,3\)

### Lemma 4.1: binary forms over a finite field represent every nonzero value

Let \(p\) be odd and let \(a,b,t\in\mathbb F_p^\times\). Then there are
\(x,y\in\mathbb F_p\) with
\[
 ax^2+by^2=t.
\]

#### Proof

The set of squares in \(\mathbb F_p\), including zero, has
\((p+1)/2\) elements. Hence each of
\[
 S_1=\{ax^2:x\in\mathbb F_p\},
 \qquad
 S_2=\{t-by^2:y\in\mathbb F_p\}
\]
has \((p+1)/2\) elements. Their cardinalities sum to \(p+1>p\), so they
intersect. An equality \(ax^2=t-by^2\) at an intersection gives the
claim. \(\square\)

### Lemma 4.2: the reduction of \(q\) has a nonsingular representation of
every value

Let \(p\ne2,3\). For every \(t\in\mathbb F_p\), there is a nonzero vector
\(v\) with
\[
 \bar q(v)=t.
\]
In particular, at least one partial derivative of \(\bar q-t\) is nonzero
at \(v\).

#### Proof

If \(t\ne0\), Lemma 4.1 gives \(X^2+Y^2=t\); take \(Z=0\). The resulting
vector is nonzero.

If \(t=0\), set \(Z=1\) and use Lemma 4.1 to solve
\[
 X^2+Y^2=-3.
\]
Again the vector is nonzero.

The gradient is \((2X,2Y,6Z)\). Because \(p\ne2,3\), it vanishes only at
the zero vector. \(\square\)

### Proposition 4.3: local universality away from \(2\) and \(3\)

For every prime \(p\ne2,3\) and every \(n\in\mathbb Z_p\), the equation
\[
 x^2+y^2+3z^2=n
\]
has a solution in \(\mathbb Z_p^3\).

#### Proof

Modulo \(p\), the determinant of \(q\) is \(3\), hence is nonzero.
Lemma 4.2 gives a nonsingular solution of \(q=n\) modulo \(p\).
Hold two coordinates fixed and apply Lemma 3.1 to the remaining coordinate,
whose partial derivative is a unit. \(\square\)

## 5. The dyadic prime

### Proposition 5.1: \(q\) represents every 2-adic integer

For every \(n\in\mathbb Z_2\), there are \(x,y,z\in\mathbb Z_2\) with
\[
 n=x^2+y^2+3z^2.
\]

#### Proof

Let \(r\in\{0,\ldots,7\}\) be the residue of \(n\) modulo \(8\).
In six cases, choose the displayed integer values of \(y,z\):

| \(r\) | \(y\) | \(z\) | \(y^2+3z^2\pmod8\) |
| ---: | ---: | ---: | ---: |
| \(0\) | \(2\) | \(1\) | \(7\) |
| \(1\) | \(0\) | \(0\) | \(0\) |
| \(2\) | \(1\) | \(0\) | \(1\) |
| \(4\) | \(0\) | \(1\) | \(3\) |
| \(5\) | \(2\) | \(0\) | \(4\) |
| \(6\) | \(1\) | \(2\) | \(5\) |

Then
\[
 u=n-y^2-3z^2\equiv1\pmod8.
\]
By Lemma 3.3, \(u=x^2\) for some \(x\in\mathbb Z_2\).

For \(r=3\), set \(x=y=0\). Then \(n/3\equiv1\pmod8\), so
\(n/3=z^2\) and \(n=3z^2\).

For \(r=7\), set \(x=2\), \(y=0\). Then
\[
 (n-4)/3\equiv1\pmod8,
\]
so \((n-4)/3=z^2\) and \(n=2^2+3z^2\).

Here division modulo \(8\) is legitimate because \(3\) is a unit in
\(\mathbb Z_2\), with \(3^{-1}\equiv3\pmod8\).

These eight cases cover \(\mathbb Z_2\). \(\square\)

No dyadic obstruction occurs. Notice that this proof uses integral
\(\mathbb Z_2\)-representations, not merely representations over
\(\mathbb Q_2\).

## 6. The prime \(3\)

For a nonzero integer \(n\), write
\[
 n=3^e u,\qquad 3\nmid u.
\]

### Lemma 6.1: sums of two squares in \(\mathbb Z_3\)

Every unit \(u\in\mathbb Z_3^\times\) is a sum of two squares in
\(\mathbb Z_3\).

#### Proof

If \(u\equiv1\pmod3\), Corollary 3.2 gives \(u=x^2\).
If \(u\equiv2\pmod3\), then \(u-1\equiv1\pmod3\), so
\(u-1=x^2\) and \(u=x^2+1^2\). \(\square\)

### Proposition 6.2: exact 3-adic criterion

Let \(n>0\), and write \(n=3^e u\) with \(3\nmid u\).
Then \(q\) represents \(n\) over \(\mathbb Z_3\) if and only if
\[
 \text{\(e\) is even}
 \quad\text{or}\quad
 \text{\(e\) is odd and \(u\equiv1\pmod3\)}.
\]
Equivalently, the only missing 3-adic values have
\[
 e\ \text{odd},\qquad u\equiv2\pmod3.
\]

#### Proof: sufficiency

If \(e=2a\), Lemma 6.1 gives \(u=r^2+s^2\). Hence
\[
 n=(3^a r)^2+(3^a s)^2+3\cdot0^2.
\]

If \(e=2a+1\) and \(u\equiv1\pmod3\), Corollary 3.2 gives \(u=t^2\).
Hence
\[
 n=3(3^a t)^2.
\]

#### Proof: necessity

Suppose
\[
 x^2+y^2+3z^2=3^{2a+1}u
 \tag{6.1}
\]
in \(\mathbb Z_3\), where \(u\) is a unit.

Reducing modulo \(3\) gives
\[
 x^2+y^2\equiv0\pmod3.
\]
The only squares modulo \(3\) are \(0\) and \(1\), so \(3\mid x\) and
\(3\mid y\). Write \(x=3x_1\), \(y=3y_1\). Dividing (6.1) by \(3\) gives
\[
 3x_1^2+3y_1^2+z^2=3^{2a}u.
 \tag{6.2}
\]

If \(a=0\), reduction of (6.2) modulo \(3\) gives
\[
 u\equiv z^2\pmod3.
\]
Since \(u\) is a unit, \(z\) is a unit and \(u\equiv1\pmod3\).

If \(a>0\), (6.2) is divisible by \(3\), hence \(3\mid z\). Thus
\(x,y,z\) are all divisible by \(3\). Dividing the original equation by
\(9\) produces
\[
 x_1^2+y_1^2+3z_1^2=3^{2(a-1)+1}u.
\]
Repeat. After \(a\) repetitions the preceding base case gives
\(u\equiv1\pmod3\). \(\square\)

### Corollary 6.3: the obstruction has the library's exact shape

For \(n>0\), the following are equivalent:

1. \(n\) is not represented by \(q\) over \(\mathbb Z_3\);
2. \(v_3(n)=2a+1\) and the 3-adic unit part is \(2\pmod3\);
3. there are \(a,b\in\mathbb N\) such that
   \[
   n=9^a(9b+6).
   \]

#### Proof

The equivalence of (1) and (2) is Proposition 6.2.

If (2) holds, write \(n=3^{2a+1}u\) with \(u=3b+2\). Then
\[
 n=9^a\cdot3(3b+2)=9^a(9b+6).
\]
Conversely, \(9b+6=3(3b+2)\) has 3-adic valuation exactly one and unit
part \(2\pmod3\). \(\square\)

## 7. The full local criterion

### Theorem 7.1

Let \(n>0\). The following are equivalent:

1. \(q\) represents \(n\) over \(\mathbb R\) and over every
   \(\mathbb Z_p\);
2. \(n\ne9^a(9b+6)\) for all \(a,b\in\mathbb N\).

#### Proof

At the real place, \(n=q(\sqrt n,0,0)\).
At \(p=2\), use Proposition 5.1.
At every \(p\ne2,3\), use Proposition 4.3.
At \(p=3\), use Corollary 6.3. \(\square\)

## 8. The one substantial rational theorem

We use the following standard theorem in exactly one place.

### Hasse--Minkowski theorem

Let \(F\) be a nondegenerate quadratic form over \(\mathbb Q\). Then
\(F\) has a nonzero zero over \(\mathbb Q\) if and only if it has a
nonzero zero over \(\mathbb R\) and over \(\mathbb Q_p\) for every prime
\(p\).

For the present proof it is applied only to
\[
 F(X,Y,Z,T)=X^2+Y^2+3Z^2-nT^2.
 \tag{8.1}
\]

If \(q\) represents \(n\) over every \(\mathbb Z_p\), then (8.1) has the
local zero \((x_p,y_p,z_p,1)\) over every \(\mathbb Q_p\). It has the real
zero \((\sqrt n,0,0,1)\). Hasse--Minkowski therefore gives a nonzero
rational zero \((x,y,z,t)\).

Because \(q\) is positive definite over \(\mathbb R\), \(t=0\) would imply
\(x=y=z=0\), contradicting nonzeroness. Thus \(t\ne0\), and division by
\(t\) gives a rational vector
\[
 v=(x/t,y/t,z/t)\in V,\qquad q(v)=n.
 \tag{8.2}
\]

This theorem is not a disguised integral regularity assumption. It supplies
only the rational vector (8.2). Sections 9--14 perform the integral lattice
work.

For formalization, Hasse--Minkowski can be proved through the usual
diagonalization, Hilbert-symbol classification over \(\mathbb Q_p\), and
Hilbert reciprocity. If it is temporarily carried as an interface, (8.1) is
the exact specialization to guard.

This input must not be under-budgeted. A standard explicit proof over
\(\mathbb Q\), such as the Borevich--Shafarevich proof summarized by Dicker,
uses Dirichlet's theorem on primes in arithmetic progressions when treating
ternary and quaternary forms. Other presentations package comparable global
arithmetic into Hilbert reciprocity and prime-existence lemmas. Thus this
document has removed a form-specific Mordell construction, but it has not
turned the global rational step into elementary congruence arithmetic.
Hasse--Minkowski is the precise remaining classical debt, and it is shared
with the rational-existence branch of the three-squares theorem.

## 9. From local integral representations to a lattice in the genus

We now prove the local-to-genus statement used in this example. The proof is
included to avoid conflating rational Hasse--Minkowski with integral
regularity.

### Lemma 9.1: equal nonzero norms are related by an orthogonal map

Let \(K\) be a field of characteristic different from \(2\), let
\((W,Q)\) be nondegenerate, and suppose
\[
 Q(v)=Q(w)=n\ne0.
\]
Then some \(\sigma\in O(W,Q)\) satisfies \(\sigma(v)=w\).

#### Proof

For \(Q(u)\ne0\), reflection in \(u\) is
\[
 s_u(x)=x-\frac{2B(x,u)}{Q(u)}u.
\]
It is an isometry.

If \(Q(v-w)\ne0\), then
\[
 2B(v,v-w)=Q(v-w),
\]
so \(s_{v-w}(v)=w\).

If \(Q(v-w)=0\), then \(B(v,w)=n\), and
\[
 Q(v+w)=4n\ne0.
\]
The reflection \(s_{v+w}\) sends \(v\) to \(-w\), and \(s_w\) sends
\(-w\) to \(w\). Thus \(s_w\circ s_{v+w}\) works. \(\square\)

This is the one-dimensional case of Witt extension, proved here explicitly.

### Lemma 9.2: patching finitely many local lattices

Let \(V\) be a finite-dimensional rational vector space and \(L\subset V\)
a full \(\mathbb Z\)-lattice. Suppose a full \(\mathbb Z_p\)-lattice
\(M_p\subset V_p\) is specified for every prime \(p\), with
\[
 M_p=L_p
\]
for all but finitely many \(p\). Then
\[
 M=\{x\in V:x\in M_p\text{ for every }p\}
 \tag{9.1}
\]
is a full \(\mathbb Z\)-lattice and
\[
 M\otimes\mathbb Z_p=M_p
\]
for every \(p\).

#### Proof

Let \(S\) be the finite set where \(M_p\ne L_p\). Choose exponents \(r_p\)
such that
\[
 p^{r_p}L_p\subseteq M_p\subseteq p^{-r_p}L_p
 \qquad(p\in S),
\]
and put \(N=\prod_{p\in S}p^{r_p}\). Then any lattice satisfying the local
conditions lies between \(NL\) and \(N^{-1}L\).

The quotient
\[
 A=N^{-1}L/NL
\]
is finite and decomposes as the direct sum of its \(p\)-primary components
for \(p\mid N\). Localization canonically identifies the \(p\)-primary
component with
\[
 N^{-1}L_p/NL_p.
\]
Under this identification, \(M_p/NL_p\) specifies a subgroup of that
component. Take the direct sum \(H\) of these specified subgroups, and let
\(M\) be its inverse image under
\[
 N^{-1}L\longrightarrow A.
\]
Then \(NL\subseteq M\subseteq N^{-1}L\), so \(M\) is a full
\(\mathbb Z\)-lattice. Localizing the direct-sum construction gives
\(M\otimes\mathbb Z_p=M_p\) at each \(p\). This inverse image is exactly
the intersection (9.1). \(\square\)

### Proposition 9.3: integral local-to-genus representation

Let \(L\) be a positive integral lattice in a rational quadratic space
\((V,Q)\), and let \(n>0\). If \(L_p\) represents \(n\) for every prime
\(p\), then there is an integral lattice \(M\) in the genus of \(L\) that
represents \(n\).

#### Proof

At the real place, positivity gives a real vector of norm \(n\). By
Hasse--Minkowski as applied in Section 8, there is a rational vector
\(v\in V\) with \(Q(v)=n\).

For each prime \(p\), choose \(w_p\in L_p\) with \(Q(w_p)=n\).
By Lemma 9.1 there is \(\sigma_p\in O(V_p,Q)\) with
\(\sigma_p(v)=w_p\). Put
\[
 M_p=\sigma_p^{-1}(L_p).
\]
Then \(v\in M_p\), and \(M_p\) is isometric to \(L_p\).

For all but finitely many \(p\), the rational vector \(v\) already lies in
\(L_p\). At those primes take \(w_p=v\), \(\sigma_p=1\), and
\(M_p=L_p\). Lemma 9.2 patches the \(M_p\) to a global lattice \(M\).

Because every \(M_p\) is integral, for \(x,y\in M\) the rational number
\(B(x,y)\) belongs to every \(\mathbb Z_p\). Hence it belongs to
\[
 \mathbb Q\cap\bigcap_p\mathbb Z_p=\mathbb Z,
\]
so \(M\) is integral. It is locally isometric to \(L\) everywhere, and
therefore lies in the genus of \(L\). Finally, \(v\in M_p\) for every \(p\),
so the intersection description gives \(v\in M\), and \(M\) represents
\(n\). \(\square\)

## 10. A small-vector bound in determinant three

The next goal is to prove directly that the genus of \(L\) has one class.
We first show that every positive integral ternary lattice of determinant
three contains a vector of norm one.

### Lemma 10.1: the two-dimensional Hermite bound

Let \(\Gamma\) be a Euclidean lattice of rank two, with covolume
\(\Delta_\Gamma\). If \(s\) is the squared length of a shortest nonzero
vector, then
\[
 s\le\frac{2}{\sqrt3}\Delta_\Gamma.
 \tag{10.1}
\]

#### Proof

Let \(u\) be shortest, so \(\lVert u\rVert^2=s\). It is primitive and can be
extended to a basis \(u,v\). Replace \(v\) by \(v-ku\), choosing \(k\in
\mathbb Z\) so that
\[
 |\langle u,v\rangle|\le\frac{s}{2}.
\]
Since \(v\ne0\), shortestness gives \(\lVert v\rVert^2\ge s\). Therefore
\[
 \Delta_\Gamma^2
 =s\lVert v\rVert^2-\langle u,v\rangle^2
 \ge s^2-\frac{s^2}{4}
 =\frac34s^2.
\]
Taking square roots gives (10.1). \(\square\)

### Lemma 10.2: a sufficient ternary Hermite bound

Let \(M\) be a positive Euclidean lattice of rank three, with Gram
determinant \(D\). If \(m\) is its minimum nonzero norm, then
\[
 m^3\le\frac{64}{27}D.
 \tag{10.2}
\]

#### Proof

Choose a shortest vector \(v\), so \(\lVert v\rVert^2=m\). It is primitive.
Let \(\pi\) be orthogonal projection to \(v^\perp\). Then
\(\pi(M)\) is a rank-two lattice: the kernel of \(\pi|_M\) is
\(\mathbb Zv\). More explicitly, extend \(v\) to a basis \(v,w_1,w_2\) of
\(M\); then \(\pi(w_1),\pi(w_2)\) form a basis of the discrete image.
If \(\Delta=\sqrt D\) is the covolume of \(M\), the base-times-height volume
formula gives the projected covolume
\[
 \Delta'=\frac{\Delta}{\sqrt m}.
\]

By Lemma 10.1, \(\pi(M)\) has a nonzero vector \(u'\) with
\[
 \lVert u'\rVert^2\le\frac{2}{\sqrt3}\frac{\Delta}{\sqrt m}.
\]
Lift \(u'\) to \(u\in M\). Subtract a nearest integer multiple of \(v\), so
that
\[
 u=u'+\alpha v,\qquad |\alpha|\le\frac12.
\]
The vector \(u\) is nonzero, so shortestness of \(v\) gives
\[
 m\le\lVert u\rVert^2
 =\lVert u'\rVert^2+\alpha^2m
 \le\frac{2\Delta}{\sqrt{3m}}+\frac m4.
\]
Thus
\[
 \frac34m^{3/2}\le\frac{2}{\sqrt3}\Delta,
\]
and squaring gives
\[
 m^3\le\frac{64}{27}\Delta^2=\frac{64}{27}D.
\]
\(\square\)

### Corollary 10.3: determinant three forces norm one

Every positive integral ternary lattice of determinant \(3\) represents
\(1\).

#### Proof

Its minimum \(m\) is a positive integer. Lemma 10.2 gives
\[
 m^3\le\frac{64}{27}\cdot3=\frac{64}{9}<8.
\]
If \(m\ge2\), then \(m^3\ge8\), a contradiction. Hence \(m=1\). \(\square\)

## 11. Splitting a norm-one vector

### Lemma 11.1

Let \(M\) be an integral lattice and \(v\in M\) satisfy \(q(v)=1\). Then
\[
 M=\mathbb Zv\perp K,
\qquad
 K=v^\perp\cap M.
\]
If \(M\) has determinant \(3\), then \(K\) has rank two and determinant
\(3\).

#### Proof

For \(w\in M\), integrality gives \(B(w,v)\in\mathbb Z\), and
\[
 w=B(w,v)v+\bigl(w-B(w,v)v\bigr).
\]
The second summand lies in \(K\). The intersection of \(\mathbb Zv\) and
\(K\) is zero because \(q(v)=1\), so this is an orthogonal direct sum.
In a basis beginning with \(v\), the Gram matrix is
\[
 (1)\oplus\operatorname{Gram}(K),
\]
and determinants multiply. \(\square\)

## 12. The binary determinant-three classification

This is the mathematical argument already checked by
`Natural.reduced_binary_determinant_three_classification`.

### Lemma 12.1: binary reduction

Every positive integral binary lattice has a basis whose Gram matrix is
\[
 \begin{pmatrix}a&b\\b&c\end{pmatrix}
\]
with
\[
 0\le2b\le a\le c.
 \tag{12.1}
\]

#### Proof

Choose a shortest nonzero vector \(e\), so \(a=q(e)>0\). It is primitive;
extend it to a basis \(e,f\). Replace \(f\) by \(f-ke\), choosing \(k\) so
that
\[
 |B(e,f)|\le a/2.
\]
Replace \(f\) by \(-f\) if necessary, making \(b=B(e,f)\ge0\). Since \(e\)
is shortest, \(c=q(f)\ge a\). This gives (12.1). \(\square\)

### Proposition 12.2

Every positive integral binary lattice of determinant \(3\) is integrally
equivalent to exactly one of the following candidates:
\[
 K_1=
 \begin{pmatrix}1&0\\0&3\end{pmatrix},
 \qquad
 K_2=
 \begin{pmatrix}2&1\\1&2\end{pmatrix}.
 \tag{12.2}
\]

#### Proof

Take a reduced basis as in Lemma 12.1. The determinant equation is
\[
 ac=b^2+3.
 \tag{12.3}
\]
The inequalities \(2b\le a\le c\) give
\[
 4b^2\le a^2\le ac=b^2+3.
\]
Multiplying the right-hand inequality by \(4\) and using the left-hand
inequality gives
\[
 4a^2\le4b^2+12\le a^2+12.
\]
Hence
\[
 3a^2\le12,
\]
so \(a\le2\).

If \(a=1\), then \(2b\le1\), so \(b=0\); (12.3) gives \(c=3\).

If \(a=2\), then \(b=0\) or \(1\). The case \(b=0\) would give
\(2c=3\), impossible. Thus \(b=1\), and (12.3) gives \(c=2\).

Finally, \(K_1\) represents \(1\), whereas every value of \(K_2\) is even.
Thus the two candidates are not integrally equivalent.
\(\square\)

Combining Corollary 10.3, Lemma 11.1, and Proposition 12.2 shows that every
positive integral ternary lattice of determinant three is equivalent to one
of
\[
 L_1=\langle1\rangle\perp K_1
     =\langle1,1,3\rangle
\]
and
\[
 L_2=\langle1\rangle\perp K_2,\qquad
 q_2(x,y,z)=x^2+2y^2+2yz+2z^2.
\tag{12.4}
\]

We do not need to prove here that the two candidates are globally
inequivalent. We need the stronger and more relevant fact that they are not
equivalent over \(\mathbb Z_2\).

## 13. The two candidates have different 2-adic genera

### Proposition 13.1

The lattices \(L_1\) and \(L_2\) in (12.4) are not isometric over
\(\mathbb Z_2\).

#### Proof

In \(L_1\), the vector
\[
 (1,0,1)
\]
is primitive and has norm
\[
 1^2+0^2+3\cdot1^2=4.
\]

We claim that every vector of \(L_2\) whose norm is divisible by \(4\) is
divisible by \(2\). Suppose
\[
 x^2+2y^2+2yz+2z^2\equiv0\pmod4.
\tag{13.1}
\]
Modulo \(2\), (13.1) gives \(x^2\equiv0\), so \(x\) is even. Therefore
\(x^2\) is divisible by \(4\), and division of the remaining congruence by
\(2\) gives
\[
 y^2+yz+z^2\equiv0\pmod2.
\tag{13.2}
\]
Over \(\mathbb F_2\), the polynomial \(y^2+yz+z^2\) is \(1\) at each of
\((1,0),(0,1),(1,1)\). Hence (13.2) forces \(y\equiv z\equiv0\pmod2\).
Thus \((x,y,z)\) is not primitive.

So \(L_1\) has a primitive 2-adic vector of norm in \(4\mathbb Z_2\), while
\(L_2\) has none. A \(\mathbb Z_2\)-isometry preserves both norm and
primitivity, so no such isometry exists. \(\square\)

## 14. The genus of \(\langle1,1,3\rangle\) has one class

### Theorem 14.1

Every positive integral lattice in the genus of
\[
 L=\langle1,1,3\rangle
\]
is integrally isometric to \(L\).

#### Proof

Let \(M\) lie in the genus of \(L\). Since \(M_p\cong L_p\) for every prime,
their determinant valuations agree at every prime: a local change of basis
multiplies a Gram determinant by the square of a
\(\mathbb Z_p^\times\)-unit. Both determinants are positive integers, so
\[
 \det M=\det L=3.
\]

By Sections 10--12, \(M\) is integrally equivalent to \(L_1\) or \(L_2\).
If \(M\cong L_2\), localization would give
\[
 M\otimes\mathbb Z_2\cong L_2\otimes\mathbb Z_2.
\]
On the other hand, genus membership gives
\[
 M\otimes\mathbb Z_2\cong L_1\otimes\mathbb Z_2.
\]
This contradicts Proposition 13.1. Hence \(M\cong L_1=L\). \(\square\)

The notation in the preceding paragraph can obscure the simple point:
classification gives two possible global lattices; local equivalence to the
original lattice at \(2\) eliminates the second one.

## 15. Assembly of the converse

### Theorem 15.1: positive targets

Let \(n>0\). If \(n\ne9^a(9b+6)\) for all \(a,b\ge0\), then
\[
 n=x^2+y^2+3z^2
\]
for some integers \(x,y,z\).

#### Proof

By Theorem 7.1, \(L_p\) represents \(n\) over every \(\mathbb Z_p\), and
\(L\) represents \(n\) over \(\mathbb R\).

By Proposition 9.3, some integral lattice \(M\) in the genus of \(L\)
contains a vector \(v\) of norm \(n\).

By Theorem 14.1, there is an integral isometry \(M\cong L\). Transporting
\(v\) through it gives a vector \((x,y,z)\in\mathbb Z^3\) with
\[
 n=x^2+y^2+3z^2.
\]
\(\square\)

### Theorem 15.2: exact characterization, including zero

For every \(n\in\mathbb N\),
\[
 \exists x,y,z\in\mathbb Z,\quad n=x^2+y^2+3z^2
\]
if and only if there do not exist \(a,b\in\mathbb N\) with
\[
 n=9^a(9b+6).
\]

#### Proof

If \(n=0\), the zero vector represents it, and it is not of the displayed
obstruction shape because \(9^a(9b+6)>0\).

For \(n>0\), the reverse implication is Theorem 15.1.

For the forward implication, suppose
\[
 n=9^a(9b+6).
\]
Corollary 6.3 says that this \(n\) is not represented even over
\(\mathbb Z_3\). An integral representation would give a
\(\mathbb Z_3\)-representation, contradiction. \(\square\)

The reverse implication of Theorem 15.2 is exactly
`Matrix.TripleSquaresConverse`.

## 16. Formalization dependency ledger

The proof breaks into the following executable lemma graph.

```text
Z_p completeness
  ├─ simple-root Hensel
  │    ├─ odd-prime square lifting
  │    └─ good-prime local representations
  └─ 2-adic unit-square lifting
       └─ p=2 local universality

p=3 valuation descent
  └─ exact obstruction 9^a(9b+6)

all local representations
  + Hasse--Minkowski for q ⊥ <-n>
  + explicit equal-norm reflections
  + finite local-lattice patching
  └─ representation by some class in the genus

2D Hermite bound
  └─ ternary minimum bound
       └─ determinant 3 represents 1
            └─ orthogonal binary complement
                 └─ two binary determinant-3 candidates
                      + primitive mod-4 invariant
                      └─ genus of <1,1,3> has one class

local representation by the genus
  + one-class genus
  └─ TripleSquaresConverse
```

### Already formalized or partially formalized

- `Natural.IsTripleSquareObstruction` has the exact source-level shape.
- The rank-four consumers and all obstruction arithmetic after the converse
  are already formalized.
- The finite binary classification in Proposition 12.2 is kernel-checked in
  `Algebra.ternary_genus_determinant_three_pilot`.
- The project already has substantial finite-field, modular-arithmetic,
  matrix, and positive-form infrastructure that can host several elementary
  pieces above.

### New foundational work

1. \(\mathbb Z_p\), completeness, valuations, and Hensel lifting.
2. Rational quadratic spaces over \(\mathbb Q_p\).
3. Hasse--Minkowski, specialized first to \(q\perp\langle-n\rangle\).
4. Local lattices and the patching lemma.
5. Euclidean lattices, covolume, orthogonal projection, and the two
   low-dimensional Hermite bounds.

### What is no longer needed for this target

- A general ternary reduction algorithm.
- Jones--Pall's table as a trusted enumeration.
- The Smith--Minkowski--Siegel mass formula.
- Spinor genera or spinor exceptions.
- A form-specific Mordell construction with separately engineered auxiliary
  primes. A proof of Hasse--Minkowski may itself use Dirichlet or equivalent
  global reciprocity machinery, as Section 8 emphasizes.
- Legendre's three-squares converse.

The geometry argument is especially useful for formalization: it replaces a
general rank-three reduced-form enumeration with a norm-one vector, an
orthogonal split, and the already verified two-variable classification.

## 17. Audit of possible hidden gaps

1. **The target \(n=0\).** Handled separately in Theorem 15.2; the
   local-to-genus argument assumes \(n>0\).
2. **Integral versus rational local representation.** Sections 4--6 produce
   vectors in \(\mathbb Z_p^3\), not merely \(\mathbb Q_p^3\).
3. **The bad dyadic prime.** It is handled by an explicit eight-row table,
   not by a good-prime lemma.
4. **The exact 3-adic unit.** The forbidden family has odd valuation and
   unit part \(2\pmod3\); no valuation-zero or even-valuation case is lost.
5. **Rational representation is not integral representation.** Section 9
   changes the lattice within its genus so that the rational vector becomes
   integral.
6. **The local lattices really globalize.** Lemma 9.2 gives the finite
   quotient/Chinese-remainder construction.
7. **The patched lattice is integral.** This follows from integrality at
   every prime and \(\mathbb Q\cap\bigcap_p\mathbb Z_p=\mathbb Z\).
8. **The one-class claim is not inferred from determinant alone.** Two
   determinant-three classes occur; Proposition 13.1 uses a genuine
   2-adic invariant to select the correct genus.
9. **The small-vector argument is quantitative enough.** It proves
   \(m^3\le64D/27\); at \(D=3\), this is \(m^3<8\), forcing the integral
   minimum \(m=1\).
10. **The norm-one splitting is integral.** The coefficient
    \(B(w,v)\) is integral because the lattice is integral and \(q(v)=1\).
11. **No circular regularity input occurs.** Hasse--Minkowski supplies a
    rational point; genus patching and class number one are then proved
    independently.
12. **Hasse--Minkowski is genuinely substantial.** It is stated exactly,
    used once, and not mislabeled as an elementary lemma. A formalization
    must prove it (and its global reciprocity/prime-existence dependencies)
    or retain a guarded classical interface.

## 18. References and comparison with the literature

- B. W. Jones and G. Pall,
  [*Regular and semi-regular positive ternary quadratic forms*](https://archive.ymsc.tsinghua.edu.cn/pacm_download/117/5599-11511_2006_Article_BF02547347.pdf).
  Their one-class tables include \((1,1,3)\). The proof above reconstructs
  this particular one-class result instead of importing the table.
- P. Doyle, J. Muskat, A. Pehlivan, and K. S. Williams,
  [*Regular ternary quadratic forms*](https://math.colgate.edu/~integers/t45/t45.pdf).
  Their table records the represented set
  \(n\ne9^a(9b+6)\) and refers to Dickson's classical result.
- J. W. S. Cassels, *Rational Quadratic Forms*, Academic Press, 1978.
  This is a standard reference for Hasse--Minkowski and rational quadratic
  spaces; bibliographic record:
  [Open Library](https://openlibrary.org/books/OL4572424M/Rational_quadratic_forms).
- L. Dicker,
  [*The Hasse--Minkowski Theorem*](https://www-users.cse.umn.edu/~garrett/students/reu/hasse_minkowski.pdf).
  This gives a short explicit proof following Borevich--Shafarevich and
  states openly where Dirichlet's theorem enters.
- For a modern explicit statement of the integral genus principle used in
  Proposition 9.3, see the discussion of local representation and genus in
  [*Local description of primitive representations by ternary quadratic
  forms*](https://link.springer.com/article/10.1007/s13366-025-00808-8).
  Proposition 9.3 supplies the nonprimitive rank-one proof needed here.
