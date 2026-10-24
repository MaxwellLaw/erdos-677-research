# The four k = 6 cubics: exact maps and the remaining completeness problem

Author: MaxwellLaw. Source audit started **2026-10-23**; artifact verification dated **2026-10-24 (Asia/Shanghai)**.

The author, MaxwellLaw, used AI as an assistive tool.

**This is an auxiliary research result. It does not solve k = 6 or Erdős #677.** The rank and full-basis flags below are Magma results, outside the Lean kernel. The exact map checks are independent SymPy calculations, also outside Lean. The later height certificates have a kernel-checked integer-polynomial layer; their canonical-height interpretation and rational-interval argument remain human mathematics with exact Python arithmetic. No external result in this directory is used as a Lean axiom.

## Inputs and executed computations

Put `Phi(T) = (T-1)(T-9)(T-25)`. The four curves are

`C_(a,b): a Phi(V) = b Phi(U)`, with `(a,b) = (1,2), (1,5), (1,10), (2,5)`.

For an original interval pair, `U=(2n+7)^2`, `V=(2m+7)^2`; hence the target includes `U>=49`, odd square roots, and `sqrt(V)-sqrt(U)>=12`. A point on a cubic is only a necessary-condition candidate until all original LCM conditions are checked. The separate elementary reduction is responsible for establishing why these four curves cover the collision problem.

The scripts were run with the official Magma calculator, **Magma 2.30-1**, in fresh sessions, with `SetSeed(550)` in each script. No GRH setting or analytic-rank assumption was enabled. The server's JSON `magma.seed` records its initial seed; the script subsequently sets 550. The four minimal equations `y^2=x^3+a2*x^2+a4*x+a6` are:

| (a,b) | (a2,a4,a6) | Basis returned by `MordellWeilGroup` |
|---|---|---|
| (1,2) | (-1,-65,261) | (5,6), (13,38), (-7,18) |
| (1,5) | (-1,-408,6912) | (12,-60), (-4,92), (78,-666) |
| (1,10) | (1,-1633,97763) | (221/4,3387/8), (14,279), (43,330) |
| (2,5) | (1,-1633,32963) | (23,-90), (17,-102), (-1,186) |

In all four cases Magma returned `Z + Z + Z`, `rankproved=true`, and `fullproved=true`. The separate model run reported trivial torsion and 2-Selmer upper bound 3 together with three independent rational points. Its informational analytic-rank line is not the justification for the rank. These are CAS certifications, not independently exported descent or saturation certificates.

`models.m` constructs `EllipticCurve(C,C![1,1,1])`, takes `MinimalModel`, expands the composite map, and calls `IsInvertible` to compute the inverse. `Inverse` alone need not compute an inverse; an earlier exploratory call failed for that reason. Only successful transcripts are included here.

The current Magma handbook describes the [Nagell construction](https://docs.magma-maths.org/ArithmeticGeometry/EllipticCurves/creation.html), [inverse-map computation](https://docs.magma-maths.org/AlgebraicGeometry/Schemes/maps.html), and [unconditional default class-group proof](https://docs.magma-maths.org/GlobalFields/NumberFieldsAndOrders/ideal-class-group.html). The current [Mordell–Weil interface documentation](https://docs.magma-maths.org/ArithmeticGeometry/EllipticCurvesOverQAndNumberFields/mordell-weil.html) specifies the separate rank and full-group flags.

## Exact maps, denominators, and integrality

`verify_k6_maps.py`, run with Python 3.14 and SymPy 1.14.0, checks by exact polynomial remainders, for every curve:

1. The forward map satisfies the stated Weierstrass equation.
2. Both coordinates of each of the two map compositions are identities in the appropriate function field.
3. The inverse map satisfies the original cubic.
4. The limiting algebraic point lies on the elliptic curve and on the inverse denominator divisor.
5. The forward image has `y<0`, and the inverse denominator is nonzero, on `V>=U>=49`.

The complete rational expressions and exact outputs are in `verify_k6_maps.output.json`. The forward x coordinate has denominator `L=bU-aV-(b-a)`, and the y coordinate has denominator `L^2`. Substituting `L=0` into the cubic gives, in order,

```
2(U-1)^2(3U-35)
40(U-1)^2(3U-19)
90(U-1)^2(11U-43)
(15/4)(U-1)^2(7U-71).
```

None vanishes for `U>=49`. The inverse formulas have a different denominator `D(x,y)`; clearing it produces a linear factor and an irreducible cubic in x. The rational exceptional affine x coordinates are respectively `65/16`, `69/4`, `977/16`, `329/16`. The script proves that `D` evaluated at the forward image is strictly negative on the target branch, so those exceptional points do not hide a target-domain solution. The point at infinity of the Weierstrass model is likewise not the image of that branch. Global classifications outside this branch would still have to handle every exceptional point explicitly.

The maps do **not** preserve integrality. Concrete exact checks include:

| (a,b) | (U,V) | (n,m) | Weierstrass image |
|---|---|---|---|
| (1,2) | (289,361) | (5,6) | (199/9,-2582/27) |
| (2,5) | (169,225) | (3,4) | (5177/49,-351630/343) |

Both interval pairs have equal LCMs, but overlap. They are not counterexamples. They demonstrate that calling `IntegralPoints` only on these Weierstrass models can omit genuine original integral points. No list produced that way can establish completeness for this task.

## Exact input for the elliptic-logarithm method

Let `alpha=(b/a)^(1/3)` denote the positive real cube root. The image `Q0` of the real point at infinity of the cubic is:

| (a,b) | x(Q0) | y(Q0) |
|---|---|---|
| (1,2) | (16+alpha)/(2-alpha) | -36 alpha^2/(2-alpha)^2 |
| (1,5) | (120+48 alpha)/(5-alpha) | -(1800+1080 alpha^2)/(5-alpha)^2 |
| (1,10) | (500+247 alpha)/(10-alpha) | -(43200+10260 alpha^2)/(10-alpha)^2 |
| (2,5) | (205+44 alpha)/(5-2 alpha) | -(900+2880 alpha^2)/(5-2 alpha)^2 |

Each x coordinate is a nonconstant rational linear-fractional function of a degree-three irrational number, so `Q0` is not rational. It must not be replaced by the elliptic curve identity. The exact verifier checks the equations modulo `a alpha^3-b`.

There are useful uniform estimates on the entire positive target branch. They are human mathematical deductions supported by the exact identities and the documented verification, **not Lean theorems in this directory**. Use the standard invariant differential `eta=dx/(2y)`. Exact differentiation along each cubic gives

`eta = -8 dV / (b Phi'(U))`.

For real `U>=49`,

`Phi'(U)-U^2 = 2(U-49)^2+126(U-49)+1631 > 0`.

Also `Phi(3U)-10 Phi(U)>0`: after writing `z=U-49`, its coefficients are

`17 z^3+2534 z^2+124068 z+1997256`.

Since `Phi` is strictly increasing above 25 and `1<b/a<=10`, the positive branch satisfies `U<V<3U`. It extends uniquely and monotonically to infinity by implicit differentiation. With `b>=2`, integration to `Q0` therefore gives the following bound for the continuous lift of the real logarithm difference:

`0 < |L(P)| = 8 integral_V^infinity dt/[b Phi'(U(t))] <= 36/V`.

The lift must later be expressed using a consistently normalized real period and logarithms; its possible period integer is part of the LLL problem. With integer `U,V`, the displayed x numerators and denominators give

`h(x(P)) <= log(747)+log(V)`.

Here `h` is the absolute logarithmic rational height. The four numerators are positive and bounded by `747V`; the absolute denominator is at most `bU+aV+(b-a)<12V`. Cancellation only improves the rational-height bound. Define the x-normalized canonical height by `H(P)=lim_j 4^(-j) h(x(2^j P))`. The [height certificates](height-bounds/README.md) now give `H(P)-h(x(P))<5` on all four models and `H(sum m_i P_i)>=sum m_i²/100` for their respective displayed triples of points. Thus for a target-branch point represented by that triple, with `M=max |m_i|`,

`0 < |L(P)| <= 26892 exp(5-M^2/100)`.

This is an upper bound only; it does not give an absolute bound on M by itself. Representation of every rational point in the displayed basis remains supported by the external Magma full-group certification. Height normalizations require care: another common canonical height is `H/2`. Magma's `SilvermanBound` bounds `h-H` from above, the opposite direction to the inequality needed here. Our bound uses the coefficient estimate for duplication to prove `H-h<=log(C)/3<5`, with the direction tracked explicitly. See also the [height-difference API](https://docs.magma-maths.org/ArithmeticGeometry/EllipticCurvesOverQAndNumberFields/over_anf.html).

The height computation uses seven exact duplications of each basis point and pairwise sum, rational logarithm enclosures, and positive rational principal minors for the pairing-matrix lower bound. `LcmSix/HeightCertificates.lean` proves the supplied integer Bézout identities, common-divisor bounds, and coefficient sums. It does not formalize the elliptic duplication formula, the real norm inequalities, canonical heights, or their quadratic-form law. Those steps and the exact arithmetic replay are documented separately; no floating-point eigenvalue is used as a certificate.

## Concrete remaining computation

[Stroeker and de Weger (1999)](https://matwbn.icm.edu.pl/ksiazki/aa/aa87/aa8743.pdf) gives an effective method for general smooth plane cubics with a rational point. [Chern (2015)](https://arxiv.org/abs/1412.6736) and its [program appendix](https://shanechern.github.io/publications/appendices/Appendix.%20Programs%20for%20%27A%20note%20on%20balancing%20binomial%20coefficients%27.pdf) illustrate the nonrational Q0 case with rank 3. The constants for those different curves cannot be imported here.

A reproducible next stage is:

1. Start with each model and full basis in the table. Recheck the Magma flags and export independently checkable rank and saturation evidence if a stronger trust claim is wanted.
2. Compute rigorous real interval enclosures for the period, the three basis logarithms, and the logarithm of the exact degree-three point Q0, all using `dx/(2y)`. Track real components and the integer period coefficient.
3. Apply an explicit elliptic-logarithm lower-bound theorem with the actual curve, degree-three field, heights, and normalizations. Verify that its hypotheses hold and calculate a valid initial integer coefficient bound M0. **No M0 has been proved here.**
4. For an integer scale C, build the four-dimensional integer lattice whose columns have identity in the first three rows and rounded `C*log(P_i)`, `C*period` in the last row. The target is `(0,0,0,round(C*log(Q0)))`. Supply interval-certified roundings, exact LLL transformations, and a rigorous lower bound on the distance from that target to the lattice. Convert this and the upper bound above into a smaller coefficient bound. Repeat as justified.
5. Enumerate the *proved* final coefficient box exactly, use the inverse maps, and retain only integer odd squares and the original disjointness and LCM conditions. Finish all exceptional-map cases. A box chosen experimentally is not complete.
6. For a Lean endpoint, the completeness proof and arithmetic certificates must be proved or checked by the Lean kernel. Neither Magma's assertion flags nor this symbolic verifier can be imported as mathematical axioms.

No David-constant computation, certified logarithm intervals, LLL distance certificate, or complete final enumeration has been executed in this directory. Earlier experimental searches of small Mordell–Weil coefficient boxes are deliberately not used as evidence of completeness and are not part of this publication set.

## Reproduction

Replay the exact height certificates from the repository root with:

```sh
python3 scripts/verify_heights.py
```

This uses Python standard-library exact arithmetic and compares every mathematical output field with the saved certificate; only the Python version metadata is excluded. The integer-polynomial layer is also checked by the project's Lean build and axiom audit. Actual validation records are maintained in [VERIFICATION.md](../docs/VERIFICATION.md).

For the exact symbolic checks, from this directory:

```sh
python3 -m venv .venv-cas
.venv-cas/bin/pip install -r requirements-cas.txt
.venv-cas/bin/python verify_k6_maps.py > reproduced-maps.json
cmp verify_k6_maps.output.json reproduced-maps.json
```

This was executed successfully on 2026-10-24 in a fresh environment for the public artifact set, using pip-cached wheels for the pinned packages; the reproduced JSON was byte-identical. The scripts do not need Lean caches or a CAS network service for these exact polynomial checks.

For the Magma computations, use an installation of Magma 2.30-1 to replay `models.m` and `mordell_weil.m`, or use the official service:

```sh
python3 run_magma.py models.m reproduced-models.json
python3 run_magma.py mordell_weil.m reproduced-mw.json
```

The remote service is not version-pinned and can upgrade. The saved complete raw JSON reports record the actual version, resource information, and output. Bases and transcript formatting can differ between versions. Inspect the mathematical claims and proof flags; do not require byte equality of remote JSON metadata. The runner checks the output text because the service can return `success=true` even after a top-level Magma error.

The original scripts, transcripts and verifier are attributable to this research effort. The public directory contains no third-party paper PDF. The 2026 reduction itself is attributed to Payam Danesh and Raoul Bianchetti, [“Prime-Power Transport and a Three-Site Reduction”](https://ijmttjournal.org/public/assets/volume-72/issue-9/IJMTT-V72I9P101.pdf), especially Section 8.2. No global originality or priority claim is made for the auxiliary elliptic models or maps.
