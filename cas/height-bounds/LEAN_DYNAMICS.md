# Kernel-checked real bounds and canonical coordinate dynamics

Author: MaxwellLaw. Checkpoint: 25 October 2026, evening (Asia/Shanghai).
The author, MaxwellLaw, used AI as an assistive tool.

The subsequent [actual elliptic bridge](../../docs/LEAN_ELLIPTIC_HEIGHT.md)
now identifies these maps and heights with Mathlib group doubling. The
remaining actual-curve quadraticity input is stated explicitly there.

This 25 October addition proves the real quartic bounds and the canonical limit for the
four actual gcd-normalized integer-coordinate maps. It formalizes a substantial
part of the height argument, including `H-h<5`. At that checkpoint it did not identify these
maps with Mathlib's elliptic-curve doubling operation. That identification
is now proved; the actual-curve pairing input and full Lean k=6 endpoint
remain unfinished. The mathematical k=6
result was already established in the earlier written/certificate proof.

## Exact objects and endpoints

`PrimitiveDynamics.Point` is a pair of integers `(p,q)` with `IsCoprime p q`.
Both signs and `q=0` are permitted. The zero pair is excluded by coprimality.
For each actual model `y²=x³+a*x²+b*x+c`, use the earlier exact polynomials

```
F(p,q)=p^4-2*b*p^2*q^2-8*c*p*q^3+(b^2-4*a*c)*q^4,
G(p,q)=4*(p^3*q+a*p^2*q^2+b*p*q^3+c*q^4).
```

Define `d=gcd(F(p,q),G(p,q))` and
`step(p,q)=(F(p,q)/d,G(p,q)/d)`, with integer divisions. The proof establishes
`d>0` and primitivity of the result before defining this total self-map.
Its naive height is `h(p,q)=log(max(|p|,|q|))`, using real casts.
The canonical value is the proved limit

`H(P)=lim_N (1/4)^N*h(step^[N](P))`.

The actual concrete models are `branch1_2`, `branch1_5`, `branch1_10`,
`branch2_5` in `LcmSix/PrimitiveDynamics.lean`. Every polynomial bound and
integer-divisor obligation in their `Model` records is discharged by a Lean
proof. The four `branch*_converges` and four `branch*_height_error` endpoints
have **only the primitive input point as a variable**. They do not assume
convergence, a hypothetical canonical height, or an external CAS certificate.

For all four maps, the generic endpoints also give `H(step P)=4*H(P)`,
uniqueness among functions with bounded difference from h and this scaling
law, and finite-iterate enclosures. For the constants below,

`4^(-N)*h(step^[N] P)-4^(-N)*log(32*R)/3 <= H(P)`

`H(P) <= 4^(-N)*h(step^[N] P)+4^(-N)*log(C)/3`.

| Branch | R (existing integral Bezout bound) | C |
|---|---:|---:|
| (1,2) | 47362584674304 | 7488 |
| (1,5) | 239541243494400000000 | 250225 |
| (1,10) | 15179797184495846400000000 | 3061008 |
| (2,5) | 42499768578278400000000 | 2801808 |

These coarse R bounds apply to every primitive input. They are deliberately
distinct from the sharper rational-point gcd bounds in
[SMALL_HEIGHT.md](../saturation/SMALL_HEIGHT.md). The lower error is wider;
the upper error is unchanged. An exact degree-ten exponential Taylor estimate
proves `exp(5)>7082479/48384>146`, and `C<=3061008<146³`.
Thus all four actual dynamics satisfy the strict endpoint `H(P)-h(P)<5`.

## Certificate and analytic layers now inside Lean

1. `DuplicationBounds.lean` proves degree-four Bernstein nonnegativity,
   interval substitution, two-chart coverage of the real projective line,
   and homogeneity.
2. `DuplicationCertificates.lean` verifies all 34 rational leaves from the
   existing small-height certificate, eight compact-chart bounds, and
   `max(|p|,|q|)^4<=32*max(|F|,|G|)` for every real p,q, on all four models.
   The reciprocal chart includes infinity; the zero real pair is handled
   separately. These are universal real inequalities, not sampled checks.
3. `DuplicationHeight.lean` proves the actual coefficient-sum upper bound
   and logarithmic transfer with explicit divisor bounds. Its specialized
   small-height defects still assume the sharper divisor bound; that local
   rational-point congruence argument is not smuggled in as an axiom.
4. `CanonicalLimit.lean` proves existence from bounded recurrence defects,
   asymmetric geometric tails, scaling, bounded-change invariance and
   uniqueness. `limUnder` is a standard limit selector; convergence is
   proved for every use that interprets it as a limit. This formalizes the
   elementary argument in Milne, *Elliptic Curves*, IV Lemmas 4.5–4.6 and the
   scaling part of Theorem 4.7 ([primary text](https://www.jmilne.org/math/Books/EC2.pdf)).
5. `PrimitiveDynamics.lean` connects those layers through the actual positive
   gcd and proves the results above with no assumed height-defect premise
   left in the four concrete endpoints. `HeightConstants.lean` supplies the
   exact real-logarithm bound.

The exporter checks byte equality between the deterministic generated Lean
certificate and the saved rational leaf data. Lean itself verifies the
expanded identities and inequalities, so the exporter is not a trusted
mathematical oracle. The previous Python verifier remains an independent
arithmetic implementation, not the logical justification for these Lean terms.

## Remaining boundary

The new H is an actual dynamical height on primitive coordinate pairs.
The actual elliptic-group connection is now proved in the linked continuation.
Proving the bounded naive parallelogram input on those curves, the strong local-square gcd bounds, full descent,
David's theorem, elliptic-logarithm integration and complete residual sieve
remain to be formalized or replaced. The unconditional convergence endpoints
do not by themselves close any of those obligations. No all-length solution
or award qualification follows from this addition.

The new Lean modules use kernel-replayed tactics and standard logical axioms;
no sorry, custom mathematical axiom, native_decide or numerical oracle is
used. Source attribution and the original mathematical/certificate history
are preserved. Actual commands, clean-checkout scope and cache reuse are in
[VERIFICATION.md](../../docs/VERIFICATION.md).
