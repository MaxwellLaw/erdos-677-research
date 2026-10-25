# Independent rank upper bounds for the four rational elliptic curves

Author: MaxwellLaw. Research checkpoint: 2026-10-25 (Asia/Shanghai).

This is a mathematical argument with independently replayable exact arithmetic.
It does not assume Magma's class-group, rank, Selmer, or full-basis flags. The
number-field and elliptic-curve theory used below is not formalized in Lean.
The elliptic curves and ordered triples are those fixed in
[the length-six certificate](../global-bound/README.md).

Put `f(t)=t³+a2*t²+a4*t+a6`, `K=Q(theta)` with `f(theta)=0`, and
`E: y²=f(x)`. All four cubics are irreducible, as certified by reduction at an
explicit small prime. Thus E(Q)[2] is trivial. The previous positive height
pairing on the three specified points proves rank at least three. We prove
rank at most three independently of the CAS rank output.

## 1. The cubic Kummer map and its support

The classical 2-descent map embeds `E(Q)/2E(Q)` in

`ker(N: K*/K*² -> Q*/Q*²)`.

On a nonidentity rational point it sends `(x,y)` to the class of `x-theta`,
whose norm is `f(x)=y²`; the identity maps to 1. There is no rational affine
2-torsion exceptional case here. This is the ordinary Kummer map followed by
the cubic-algebra description of `H¹(Q,E[2])`. Its construction is compatible
with extension to Q_p, including the special formulas at local 2-torsion.
A primary source is Cremona, Fisher, O'Neil, Simon and Stoll,
[Explicit n-Descent on Elliptic Curves III, Section 3](https://mathe2.uni-bayreuth.de/stoll/papers/Explicit-Descent-III.pdf),
which states the norm-kernel identification and the `x-e_i` formulas.
If using its short Weierstrass convention, substitute `x' = x+a2/3`
and `theta' = theta+a2/3`. This gives a rational isomorphism with short
Weierstrass form and leaves `x-theta` unchanged, globally and locally.
Only this standard descent theorem is used; no computed Selmer group is
accepted from a CAS.

Take rational prime sets `S={2,3}` in the (1,2) case and `S={2,3,5}` in the
other three cases. Let `K(S,2)` mean squareclasses with even valuation at every
prime ideal not above S. Every rational point's Kummer class belongs to it:

* Write `x=X/Z²`, `y=Y/Z³`, with Z positive and `gcd(X,Z)=1`.
  These denominator forms follow from the integral monic Weierstrass equation:
  when `v_p(x)<0`, its cubic term has strictly smaller valuation than the
  lower terms, so `2v_p(y)=3v_p(x)` and `v_p(x)` is even.
  If p divides Z, theta is integral at every prime above p, and
  `v_P(x-theta)=v_P(x)=e(P/p)*v_p(x)` is even.
* Suppose p does not divide Z and p is outside S. The independently certified
  indices `[O_K:Z[theta]]` are `6,120,270,90`; their prime factors all lie in
  S. Dedekind's factorization theorem therefore describes primes above p by
  the irreducible factors of f modulo p. If `x-theta` lies in such a prime,
  its residue theta equals the rational residue x. That factor is linear.
* If f'(x) is nonzero modulo p, there is exactly one such prime, of residue
  degree one. All other valuations are zero. The norm identity `y²` forces
  this remaining valuation to be even. If f(x) is nonzero modulo p, all
  valuations are zero directly.
* The only possible obstruction is a repeated residue root r. The power-basis
  discriminants, factorizations and all such roots outside S are checked in
  `rank_support.json`. For every one, `f(r)` is nonzero modulo p² while
  `f(r)=f'(r)=0` modulo p. Every lift `r+p*t` has
  `f(r+p*t)=f(r) mod p²`, hence valuation exactly one. This contradicts
  `f(x)=y²` for the p-integral rational point. The argument applies to rational
  p-adic lifts as well as integer lifts. Thus this case cannot occur.

This explicitly excludes the large discriminant primes; it does not assume
that the set S printed by Magma is sufficient. Define
`V=ker(N: K(S,2) -> Q*/Q*²)`. We have proved that the global Kummer image lies
in V and that its localization lies in the local Kummer image at every prime.

## 2. Global squareclass dimensions

The independently verified maximal orders have negative discriminants, hence
signature (1,1). The ordinary unit squareclass group has dimension two by
Dirichlet's unit theorem: rank one and torsion {1,-1}. For the set S_K of
prime ideals above S, the S-unit squareclass dimension is `2+|S_K|`.
The valuation/ideal-class exact sequence is

`0 -> O_(K,S)*/O_(K,S)*² -> K(S,2) -> Cl_(K,S)[2] -> 0`.

The [ideal certificates](IDEAL_CERTIFICATES.md) prove completeness of the
maximal orders, all prime-ideal decompositions through a safe Minkowski bound,
and explicit odd-power principal relations for every prime ideal in the
Minkowski generating set. These relations give the following upper bounds;
no assertion that a CAS-computed class group is complete is required.

| (a,b) | #S | #S_K | dim Cl_(K,S)[2] upper | dim K(S,2) upper | dim V upper |
|---|---:|---:|---:|---:|---:|
| (1,2) | 2 | 4 | 0 | 6 | 3 |
| (1,5) | 3 | 7 | 0 | 9 | 5 |
| (1,10) | 3 | 4 | 1 | 7 | 3 |
| (2,5) | 3 | 4 | 1 | 7 | 3 |

For a finite class group, the dimensions of its quotient by 2 and its
2-torsion agree; this justifies using the verified mod-2 relations in the
exact sequence. The norm image has dimension exactly `|S|+1`. Its support is
contained in the rational squareclasses generated by -1 and S, and it contains
all of them: rational S-units are elements of K(S,2), and a rational number's
norm in this cubic field is its cube. Subtracting this norm-image dimension
proves the last column. Three curves consequently already have rank at most
three. No fundamental-unit generator assumption is needed for this dimension
upper bound; the additional unit-squareclass witnesses are independently
checked supplementary data.

## 3. The remaining (1,5) curve at 3

The [local certificate](local3/README.md) supplies three distinct Hensel roots
of `t³-t²-408t+6912` in Q_3. Therefore `K tensor Q_3` is `Q_3³`, and the local
squareclass space is `(Q_3*/Q_3*²)³`, of dimension six. Each Q_3 component is
encoded by its valuation parity and its unit modulo 3.

Four explicit algebraic integers have norms `2^54,2^54,3^54,3^54`. Hence their
principal ideals are supported on primes above S, and their norm-square
classes belong to V. Two exact implementations verify integrality, norms,
Hensel precision, the six local bits, and an odd 4-by-4 minor. Their local
images are independent. Thus the restriction of localization to V has rank
at least four. Since `dim V<=5`, its kernel has dimension at most one.

The local Kummer image has dimension two. Indeed the three distinct roots give
`E(Q_3)[2]` dimension two. Multiplication by 2 is an automorphism of the open
formal group E_1(Q_3), and `E(Q_3)/E_1(Q_3)` is finite. For a finite abelian
group its 2-torsion and quotient by 2 have the same order; the multiplication
by 2 exact sequence therefore gives
`dim E(Q_3)/2E(Q_3)=dim E(Q_3)[2]=2`.
This uses the formal-group statement for an integer prime to 3, not an
assumption of good reduction at 3. See Milne,
[Elliptic Curves, II Section 4, especially Corollary 4.2(a)](https://www.jmilne.org/math/Books/EC2.pdf).

The preimage in V of the local Kummer image has dimension at most `1+2=3`.
The global Kummer image lies in that preimage. This proves the missing rank
upper bound without computing the entire local Kummer image or treating a
reported local Selmer dimension as a certificate.

## 4. Full generation and the fixed-length conclusion

All four ranks are exactly three. The independent
[saturation and minimum-height proof](../saturation/SMALL_HEIGHT.md) proves
that each displayed subgroup G is fully saturated in E(Q), with no rank
assumption: its saturated hull has rank three and index less than 80, while
finite-field certificates exclude every prime divisor of that index. The
same finite-field data prove E(Q) is torsion-free. Since E(Q) and G now have
the same rank, their quotient is both finite and torsion-free, so G=E(Q).

The old full-basis flags can thus be retained as cross-checks rather than
proof assumptions. Combining this independent group certificate with the
[analytic bounds and complete residual exclusion](../global-bound/README.md)
proves the mathematical/computational statement

`for every n,m in N with m>=n+6, M(n,6) != M(m,6)`.

This remains a fixed-length result. No complete Lean theorem with that endpoint
has been established, and no statement for arbitrary positive k follows.
The standard number-field, local-field, Kummer, canonical-height and analytic
theorems in the written argument and the exact Python arithmetic remain outside
Lean; the separately listed kernel-checked lemmas do not conceal them as axioms.
