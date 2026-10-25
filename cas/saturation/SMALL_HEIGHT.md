# A global minimum-height certificate and complete saturation

The files `certify_small_height.py`, `small_height_certificate.json`, and
`verify_small_height.py` establish the following result using exact arithmetic
and the standard theory of the canonical height. No Magma height, rank,
minimal-model, or saturation flag enters the computation.

For each of the four curves

| pair | a,b,c in y²=x³+a x²+b x+c | D | B |
|---|---|---:|---:|
| (1,2) | -1,-65,261 | 4608 | 19 |
| (1,5) | -1,-408,6912 | 460800 | 86 |
| (1,10) | 1,-1633,97763 | 9331200 | 234 |
| (2,5) | 1,-1633,32963 | 1036800 | 113 |

write `h(P)=log max(|p|,q)` when `x(P)=p/q` is reduced with `q>0`, and
`h(O)=0`. Use exactly the existing x-coordinate normalization
`H(P)=lim 4^(-j) h(2^j P)`.

**New conclusions.** Every nonzero rational point satisfies `H(P)>1/10`.
The three specified generators span a **fully saturated** rank-three
subgroup of `E(Q)`: if `n*P` is in that subgroup for a positive integer `n`,
then `P` is in it. The separate [rank upper bound](../descent/RANK_PROOF.md) now implies that
these generators span all of `E(Q)`. This directory proves saturation; the
rank argument is carried out in that separate certificate.
These are human mathematical consequences of the replayable certificates,
not complete Lean theorems about elliptic-curve heights or reduction.

## 1. The duplication map and primitive gcd

Put

```
f(x) = x^3+a*x^2+b*x+c
F(p,q) = p^4-2*b*p^2*q^2-8*c*p*q^3+(b^2-4*a*c)*q^4
G(p,q) = 4*(p^3*q+a*p^2*q^2+b*p*q^3+c*q^4).
```

The duplication formula is `x(2P)=[F(p,q):G(p,q)]` projectively; this includes
points doubled to `O`, as well as `O=[1:0]` itself. The four curves are smooth.
Two exact homogeneous degree-seven identities are included for each curve:

```
U_p F + V_p G = R_p p^7,
U_q F + V_q G = R_q q^7.
```

The coefficients arise by dividing each earlier integral Bezout identity
by the gcd of all its coefficients and its right-hand scalar. Both programs
verify every coefficient of both identities. For coprime `p,q`, the positive
gcd `g=gcd(F(p,q),G(p,q))` divides `R_g=lcm(R_p,R_q)`: at each prime, at least
one of `p,q` is a unit, and the corresponding identity bounds the valuation
of `g` by that of `R_p` or `R_q`, hence by the maximum. The values of `R_g` are

```
1720512, 3869280000, 974031480000, 51538680000.
```

This already proves the pair `(F,G)` never vanishes simultaneously on a
primitive pair; in particular projective exceptional points create no
undefined height.

The following improvement uses that `p/q` is the x-coordinate of a rational
point, not an arbitrary rational number. If a prime `ell` divides `q`, then
`F(p,q)` is a unit modulo `ell`, so `ell` does not divide `g`. Otherwise `x`
is integral at `ell`, and so is `y`, since `y²=f(x)`. Multiplication by the
unit `q^4` identifies the gcd valuation with

```
min(v_ell(F(x,1)), v_ell(G(x,1))).
```

For every prime dividing `R_g`, the certificate verifies an upper bound
on this minimum as follows.

* At `ell=2,3,5`, put `e=v_ell(R_g)` and `M=ell^(e+1)`. Enumerate **all**
  residue classes `x mod M` for which `f(x)` is a square modulo `M`. For each,
  compute the minimum valuation of `F(x,1),G(x,1)`. It is at most `e`, so
  reduction modulo `M` determines that minimum for every lift. These classes
  include the reduction of every actual rational point integral at `ell`.
* At each remaining prime, enumerate all roots with `f(s)=f'(s)=0 mod ell`
  and check `f(s) != 0 mod ell²`. The polynomial identity
  `F(x,1)=f'(x)^2-4(a+2x)f(x)` shows that a common zero of `F,G` modulo this
  odd prime must be such a root. For any lift `x=s+ell*t`, Taylor expansion
  gives `f(x)=f(s) mod ell²`; but `y²=f(x)` and `y=0 mod ell` would imply
  `f(x)=0 mod ell²`, a contradiction. Thus these primes cannot divide `g`.

The record contains the full factorization of `R_g`, the singular roots,
the nonzero residues modulo `ell²`, and exact counts by gcd valuation for
every eligible small-prime residue. The resulting bounds are

| pair | maximum exponents at 2,3,5 | g_max |
|---|---|---:|
| (1,2) | 4,2,0 | 144 |
| (1,5) | 6,2,2 | 14400 |
| (1,10) | 4,6,2 | 291600 |
| (2,5) | 4,4,2 | 32400 |

No minimal-model claim or Tate-algorithm output is needed for this step.

## 2. A rational polynomial certificate for the real absolute value

For each curve, the certificate proves

```
max(|F(x,1)|, |G(x,1)|) >= max(1,|x|)^4 / 32
```

for every real `x`. It uses two compact charts. On `-1<=x<=1` it treats
`F(x,1),G(x,1)` directly. On `|x|>=1`, use `t=1/x` and the reciprocal
polynomials `t^4 F(1/t,1), t^4 G(1/t,1)` on `[-1,1]`. Including `t=0`
is harmless and also covers the limit at infinity.

Each chart is partitioned into closed rational intervals with no gap. On
an interval `[L,U]`, the record selects one polynomial `P` and a sign `s`,
and expresses `32*s*P(L+(U-L)t)-1` in the degree-four Bernstein basis
`binom(4,j)*t^j*(1-t)^(4-j)`. Every recorded coefficient is nonnegative.
All basis functions are nonnegative on `[0,1]`, which proves the required
inequality throughout that interval. The complete partitions contain only
6, 8, 11, and 9 leaves, respectively, counting both charts.

The discovery program computes Bernstein coefficients from the power
coefficients. The independent verifier instead expands the proposed
Bernstein basis back into ordinary powers and checks exact equality, as
well as interval coverage and coefficient signs. There are no approximate
root locations or floating-point sign decisions in the proof.

Homogeneity now gives
`max(|F(p,q)|,|G(p,q)|) >= max(|p|,|q|)^4/32` for every real pair. Dividing
by the actual primitive gcd, bounded by `g_max` in section 1, gives

```
h(2P) >= 4 h(P) - log D,       D=32*g_max.
```

This also holds at `O`. Iteration and summing the geometric series give the
**global** bound, on every rational point,

```
H(P) >= h(P) - (log D)/3.
```

Unlike the earlier subgroup pairing bound, this inequality applies to
points outside the three-generator subgroup as well.

## 3. Completeness of the tiny height box

Suppose `P != O` and `H(P)<=1/10`. Then
`max(|p|,q) <= exp(1/10)*D^(1/3)`. The exponential series gives
`exp(1/10)<1/(1-1/10)=10/9`. The recorded integer `B` satisfies
`729*B^3 >= 1000*D`, so `max(|p|,q)<B`; enumerating the inclusive box of
size `B` is conservative.

For an integral Weierstrass equation of the present shape, the denominator
of the reduced x-coordinate is a square. Indeed, at a prime where `v(x)<0`,
the cubic term uniquely has the lowest valuation in `f(x)`, so
`2v(y)=3v(x)`; consequently `v(x)` is even. Thus uniquely

```
x = X/Z^2, y = Y/Z^3, Z>0, gcd(X,Z)=1,
Y^2 = X^3+a X^2 Z^2+b X Z^4+c Z^6.
```

Every point with `H<=1/10` therefore occurs among
`1<=Z<=floor(sqrt B), -B<=X<=B`. The programs enumerate that entire box
and test the last integer for being an exact square. Up to changing the
sign of `y`, there are 11,12,14,14 points in the four boxes, respectively.
These 51 points are unrelated to the earlier 46 survivors in the original
cubic-equation coefficient sieve; the domains and purposes differ.

For every one of the 51 points, two exact doublings give
`x(4P)=p_2/q_2` in lowest terms, `q_2>0`, and `N=max(|p_2|,q_2)` satisfies

```
N^3 > 1024*D.
```

The global lower-height inequality applied to `4P` and quadraticity imply

```
H(P) = H(4P)/16
     >= (log N - (log D)/3)/16
     > (10 log 2)/48
     > 5/48
     > 1/10.
```

Here `log 2>1/2` follows by integrating `1/t>1/2` on `1<t<2`. This contradicts
the assumption and proves `H(P)>1/10` for every nonzero rational point.
There are no unhandled points doubled to infinity: none occurs in the
exhaustive box, and the global height estimate was projective. The verifier
checks the displayed doublings by the ordinary rational tangent addition
formula with the y-coordinate, separately from the discovery program's
homogeneous duplication calculation.

## 4. From minimum height to complete saturation

Let `G` be the specified rank-three subgroup; independence is already proved
by the positive height-pairing certificate. Let

```
S = { P in E(Q) : n*P is in G for some integer n>0 }.
```

By Mordell–Weil, and the torsion-freeness independently proved by the finite
reduction certificate, `S` is a free rank-three group, `G` has finite index
`I` in `S`, and the positive canonical pairing identifies them with nested
Euclidean lattices. **This construction does not assume rank(E(Q))=3.**
The regulator uses the pairing with diagonal entries `H(P_i)`, precisely
the normalization used throughout this project.

The previously certified pairing intervals give `Reg(G)<8/5` for all four
curves. The new verifier independently bounds the determinant at all 512
corners of the nine-entry interval box; a determinant is affine in each
matrix entry, so the corner extrema bound the determinant everywhere in
that box. It does not assume that endpoint matrices retain symmetry.

Since every nonzero vector of `S` has squared length greater than `mu=1/10`,
the closed radius-`sqrt(mu)` ball contains no nonzero lattice point.
Minkowski's convex-body theorem in dimension three implies

```
(4*pi/3)*mu^(3/2) < 8*covol(S).
```

Even the weaker non-strict version suffices, because `pi>3`. Squaring yields

```
Reg(S) >= (pi^2/36)*mu^3 > mu^3/4 = 1/4000.
```

The index relation `Reg(G)=I^2*Reg(S)` therefore gives
`I^2 < (8/5)*4000 = 6400`, hence `I<80`.

If `I>1`, a prime divisor `ell` of `I` is at most 79. The finite abelian group
`S/G` then has an element of order `ell`, contradicting the independently
certified ell-saturation for every prime at most 101. Thus `I=1` and `G=S`:
**G is completely saturated in E(Q).** Extra independent directions in
`E(Q)` are not excluded by saturation alone. The separate
[independent rank proof](../descent/RANK_PROOF.md) supplies rank at most three
and therefore concludes `G=E(Q)` without a CAS basis flag.

For the general lattice theorem, see Conrad–Landesman, *Undergraduate Number
Theory*, Theorem 27.9 and its proof:
<https://math.stanford.edu/~conrad/154Page/handouts/undergraduate-number-theory.pdf>.
For the standard height-and-regulator saturation strategy, see Siksek,
*Infinite Descent on Elliptic Curves*, Rocky Mountain Journal of Mathematics
25 (1995), 1501–1538, section 3, author copy:
<https://samirsiksek.github.io/siksek.github.io/papers/infart2.pdf>.
The duplication, local congruence, real polynomial, and finite-box bounds
above are supplied explicitly rather than relying on an implementation of
those general methods.

## Actual replay and scope

From the repository root:

```sh
python3 cas/saturation/certify_small_height.py
python3 cas/saturation/verify_small_height.py
```

Both ran successfully on 25 October 2026 using Python 3.14.6 and only the
standard library. Keep assertions enabled. Certificate SHA256:
`61dbc9566c9dee8a3e3cbfcbf5b34ca0c746e2a0dea4fba838d74a19730c5075`.
Independent verifier SHA256:
`b77d1e0248cff2e30594f5b37e9322caaae9018904de5e4ddb5e51dd1aca1d33`.

The two input JSON hashes are fixed in the certificate. The stronger
primitive-gcd bound does not assume the arithmetic objects are rational
points merely because a CAS returned them: the local-square constraints
are logically necessary for arbitrary rational points, and every enumerated
box point is checked on the exact original Weierstrass equation.

These computations and the documented proof close the finite-index/saturation layer of the
full-group question. Independent exact replay has passed; the height and group arguments remain subject to mathematical review. They do
not establish a rank upper bound, do not themselves solve all lengths,
and do not provide a complete Lean `k=6` endpoint. The analytic use of the
canonical height and Minkowski theorem and the finite-field reduction
interpretation remain outside Lean in this directory.

## Subsequent formalization of the real bound

The 34 Bernstein leaves, complete real-chart coverage and universal quartic
lower bounds from section 2 are now kernel checked in
`LcmSix/DuplicationCertificates.lean`. The associated logarithmic transfer
and canonical coordinate dynamics are described in
[LEAN_DYNAMICS.md](../height-bounds/LEAN_DYNAMICS.md). This does not formalize
the strong local-square gcd bound, tiny-box exhaustion, global minimum-height
argument or lattice-index proof in the other sections of this document.
