# Rigorous algebraic-height inputs for David's lower bound

Research checkpoint, 2026-10-24. These are human mathematical deductions with
exact arithmetic checks, not Lean proofs. This note supplies curve and point
height parameters; it supplies no certified elliptic periods, effective
coefficient bound M0, complete point enumeration, or solution of k=6.

The primary normalization was checked directly in Sinnou David,
[Minorations de formes linéaires de logarithmes elliptiques](https://smf.emath.fr/system/files/filepdf/MSMF_1995_2_62__1_0.pdf),
Mémoires SMF 62 (1995), printed pp.9–10, especially the definitions preceding
Théorème 2.1. The inspected source and its SHA256 are recorded in
`INITIAL_BOUND.md`; the PDF and page images are not vendored. David uses absolute logarithmic Weil
height on projective space and the plane-cubic canonical height
`hat_h_D(P)=lim_(n→∞) h([n]P)/n²`.

## Exact model and curve-height parameters

Start with `y²=x³+a2*x²+a4*x+a6` and make the group isomorphism

```
z=x+a2/3,  w=2y,
w²=4z³-g2*z-g3,
g2=-4(a4-a2²/3),
g3=-4(a6-a2*a4/3+2a2³/27).
```

The standard differential is unchanged: `dz/w=dx/(2y)`. No extra factor of two
in the elliptic logarithms is introduced by this David-model conversion.

The exact parameters are:

| pair | g2 | g3 | primitive coordinates [1:g2:g3] | j |
|---|---|---|---|---|
| (1,2) | 784/3 | -25840/27 | [27:7056:-25840] | -120472576/26883 |
| (1,5) | 4900/3 | -731800/27 | [27:44100:-731800] | -11764900/24183 |
| (1,10) | 19600/3 | -10617200/27 | [27:176400:-10617200] | -3011814400/24350787 |
| (2,5) | 19600/3 | -3618800/27 | [27:176400:-3618800] | -3011814400/1288467 |

Here `j=1728*g2³/(g2³-27*g3²)`; every denominator is nonzero. The maximum
integer appearing in either the primitive curve coordinates or the primitive
numerator/denominator of j is, respectively,

```
120472576, 11764900, 3011814400, 3011814400.
```

Thus David's `h=max(1,h([1:g2:g3]),h(j))` is **strictly less than 22** in all
four cases. The logarithm comparison is certified without floating point:

```
exp(22) > sum_(j=0)^27 22^j/j!
        = 6749346963996500262098856679/2145544448257153125
        > 3011814400.
```

Heights here are absolute heights. Passing from Q to the degree-three field
containing Q0 does not multiply these rational curve heights by three.

## Extending the existing duplication bounds to all algebraic points

The known integer quartics F,G and cubic witnesses satisfy

```
U*F+V*G=R*p^7,  U'*F+V'*G=R*q^7,  R!=0.
```

Let `C` be the maximum coefficient absolute sum of F,G, and `D` the maximum
combined coefficient absolute sum of the two witness pairs. For any number
field K and any homogeneous pair p,q in K, put at a place v

```
Bv=max(|p|v,|q|v),  Kv=max(|F(p,q)|v,|G(p,q)|v).
```

There is no simultaneous zero of F,G, as follows already from the two
identities. At an archimedean place the triangle inequality gives

```
|R|v*Bv^4/D <= Kv <= C*Bv^4.
```

For the lower bound choose the identity with the dominant input coordinate.
At a nonarchimedean place all integer coefficients have absolute value at most
one, so the ultrametric inequality gives the stronger local bounds

```
|R|v*Bv^4 <= Kv <= Bv^4.
```

Summing logarithms with the absolute-height weights, the product formula
cancels the contribution from R. The archimedean weights sum to one. Therefore
for every algebraic point P, including infinity,

```
-log D <= h(x(2P))-4h(x(P)) <= log C.
```

The geometric telescoping argument proves existence of Hx and yields the same
bounds as over Q:

```
-log D/3 <= Hx(P)-h(x(P)) <= log C/3,
Hx(P)=lim_j 4^(-j) h(x(2^j P)).
```

In particular the existing integer comparisons `C<146³` and
`exp(5)>7082479/48384>146` imply

```
Hx(P)-h(x(P)) < 5
```

for **all algebraic points**, not only rational ones. No extrapolation from
rational test points or numerical heights is involved.

## The degree-three point Q0

Write `alpha=(b/a)^(1/3)>1`. In each branch `a*T³-b` is irreducible over Q:
the ratio b/a is not a rational cube, as is seen from the exponent of 2 or 5
in its prime factorization. Thus K=Q(alpha) has degree exactly three. Its
three conjugates have absolute value alpha, and the primitive minimal
polynomial gives

```
h(alpha)=log(b)/3.
```

The supplied exact maps give

```
x(Q0)=(c+d*alpha)/(b-a*alpha),
(c,d)=(16,1),(120,48),(500,247),(205,44)
```

in branch order. The denominators are nonzero; otherwise alpha=b/a would be
rational. The linear-fractional determinants have nonzero absolute value
`a*c+b*d`, so x(Q0), and hence Q0, have degree exactly three. The already
verified y-coordinate formulas belong to the same field.

At every nonarchimedean place the integral coefficient matrix of this
linear-fractional map has norm at most one; at every archimedean place its row
absolute sums are bounded by `T=max(c+d,a+b)`. Consequently

```
h(x(Q0)) <= h(alpha)+log T = log(b)/3+log T.
```

The exact T values are 17,168,747,249. Uniformly `T<=747` and `b<=10`.
The finite positive exponential series give

```
exp(7) > sum_(j=0)^8 7^j/j! = 4605383/5760 > 747,
exp(3) > 1+3+9/2+27/6 = 13 > 10.
```

Hence `h(x(Q0))<8`, and the algebraic duplication estimate proves

```
Hx(Q0)<13.
```

## Converting x-height to David's plane-cubic height

For the affine David model put at each place
`Bv=max(1,|z|v)` and `Tv=max(1,|z|v,|w|v)`.
The equation and its rearrangement

```
w²=4z³-g2*z-g3,
4z³=w²+g2*z+g3
```

show that `Tv²/Bv³` is bounded above and bounded away from zero by constants
depending only on g2,g3 at that place. For clarity, valid archimedean
inequalities are

```
Tv² <= max(1,4+|g2|v+|g3|v)*Bv³,
Bv³ <= max(1,(1+|g2|v+|g3|v)/4)*Tv².
```

At a nonarchimedean place, replace the corresponding constants by

```
max(1,|4|v,|g2|v,|g3|v),
max(1,|1/4|v,|g2/4|v,|g3/4|v).
```

They equal one away from a fixed finite set of places. Summing gives

```
h([1:z:w]) = (3/2)h(z) + O_E(1).
```

Infinity has zero height in both conventions. Also `z=x+a2/3`, where
`a2=±1`, changes h(x) by at most log4: the forward and reverse maps have
homogeneous coordinates `[3p±q:3q]` and archimedean coefficient norm at most
four. These bounded differences disappear after dividing by `4^j`. Taking
the subsequence n=2^j in David's canonical-height definition therefore gives

```
hat_h_D(P) = (3/2)Hx(P).
```

This is a proved normalization factor, not an assumption based on the common
half-x-height convention. In particular

```
hat_h_D(Q0) < 39/2 < 20.
```

All twelve displayed rational basis points have certified `Hx(Pi)<5`, as
verified by reading the upper endpoints of the existing exact intervals.
Therefore `hat_h_D(Pi)<15/2<8`. The identity, when a period is represented as
a logarithm of it, has canonical height zero.

## Usable parameter values and boundary

For David's theorem the choices `log(Vi)>=22` cover all the algebraic-height
and curve-height terms for the three basis logarithms, the Q0 logarithm and
the period/identity logarithm. They are not yet a complete admissible choice:
one must also prove

```
log(Vi) >= 3*pi*|ui|²/(D*|omega1|²*Im(tau)),
```

choose compatible lifts and a reduced period basis, meet the E conditions,
and handle the coefficient B thresholds. Here D=3. Neither period estimates
nor those remaining steps are certified by this note. It therefore proves
no M0. Applying any eventual bound to every rational point also retains the
separate full-Mordell-Weil-group obligation currently supported by Magma's
flags, not a new claim made here.

Reproduction from this directory:

```
python3 height_parameters.py
```

`height_parameters.json` records the exact rational computations, positive
series comparisons, input hashes, and basis upper endpoints. It uses Python
standard-library integers and Fractions only. Mathematical field-height,
product-formula, convergence and model-normalization reasoning is in this
note, outside the Lean kernel.
