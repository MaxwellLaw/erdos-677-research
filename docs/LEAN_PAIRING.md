# Actual canonical pairing in the pinned project

Author: MaxwellLaw. Checkpoint: 26 October 2026, evening.
The author, MaxwellLaw, used AI as an assistive tool.

The four actual rational elliptic groups now satisfy the bounded naive
parallelogram law, the exact canonical parallelogram law, a symmetric
biadditive canonical pairing, all integer quadraticity laws and a finite
Gram expansion in Lean. The previously explicit bounded-defect premise has
been proved for these curves. The complete Lean k=6 endpoint and the
all-length problem remain unfinished.

## Prior formalization and the scope of this integration

Michael Stoll already formalized the general compatibility identity in
Mathlib main at commit
[`69fe4f49ffbc9580a2c3ae6d29591ef6d1d4131e`](https://github.com/leanprover-community/mathlib4/commit/69fe4f49ffbc9580a2c3ae6d29591ef6d1d4131e),
`Point.sym2x_add_sub_eq_addSubMap_sym2x`, and the general approximate
parallelogram theorem at
[`751af11de0208780dda5326b40c54b3859607d03`](https://github.com/leanprover-community/mathlib4/commit/751af11de0208780dda5326b40c54b3859607d03),
`WeierstrassCurve.Affine.approx_parallelogram_law`.
The associated PRs are [43292](https://github.com/leanprover-community/mathlib4/pull/43292)
and [43463](https://github.com/leanprover-community/mathlib4/pull/43463).
The verified main commits establish their integration; the closed PRs' raw
merged flag is not used as evidence because Bors integrated them.

Our checked project remains pinned to Mathlib
`0df444a360eaa60ab8c11dca51a86af692955474` and Lean 4.33.1. That pinned
version retains the compatibility/approximate-law TODOs. It already proves
Stoll's polynomial-map height estimate
`abs_logHeight_addSubMap_sub_two_mul_logHeight_le`, which is directly reused.
No claim is made to the first formalization of the compatibility or
parallelogram theorem. The contribution here is the fixed-version
specialization, its connection to this project's explicit coordinate-height
limit, the concrete canonical endpoints and their verification.

The new compatibility proof is restricted to rational models
`y^2=x^3+a*x^2+b*x+c`, meaning a1=a3=0; it does not claim to replace the
more general current Mathlib theorem. Mathlib's polynomial, height and group
APIs retain their original attribution, including Michael Stoll, Ralf
Stephan and David Kurniadi Angdinata. Standard canonical-height theory is
also credited in `CanonicalQuadratic.lean` and [the earlier note](LEAN_ELLIPTIC_HEIGHT.md).

## Addition and subtraction on actual points

`EllipticAddSub.addSubMap_sym2x` proves for every actual nonsingular point
pair P,Q of the displayed rational model that there exists a nonzero rational
r with

```
eval(addSubMap)(P.sym2x Q) = r • (P+Q).sym2x(P-Q).
```

This uses the existing Mathlib map and actual point-group operations.
The finite distinct-x case has scalar `(x(P)-x(Q))^2`; the two curve equations
prove both product and sum identities after clearing the nonzero denominator.
For equal x, the actual points are equal or negatives. The existing
`quartic_xRep_double` handles their diagonal/antidiagonal cases, including
two-torsion and infinity. Either zero input has scalar one. There is no
excluded chart, assumed map identity or CAS input.

## The bounded defect and exact canonical endpoint

The projective height is invariant under the proved nonzero scalar. Stoll's
polynomial height estimate bounds the difference between the output height
and twice the input height by D. His symmetric-square estimate bounds the
difference between each symmetric height and the corresponding sum of two
x-heights by C. The actual naive parallelogram defect is the map error minus
the output symmetric error plus twice the input symmetric error, giving
`D+3*C` uniformly.

`EllipticParallelogram.naiveHeight_boundedDefect` proves that statement;
`canonical_parallelogram` applies the previously checked limiting theorem.
The canonical value is definitionally the existing actual group-doubling
limit from `EllipticDuplication.canonicalHeight`.

`canonicalPairing` constructs an actual group bi-homomorphism
`E(Q) ->+ E(Q) ->+ Real`, with

```
B(P,Q)=(H(P+Q)-H(P-Q))/4,
B(P,P)=H(P),
H([n]P)=n^2*H(P)  for every integer n.
```

This is the project's x-height normalization. Nonnegativity follows from
the already proved convergence of nonnegative projective heights. For every
finite set of points and integer coefficients, `canonical_sum_zsmul` proves

```
H(sum_i n_i P_i)=sum_i sum_j n_i*n_j*B(P_i,P_j).
```

Four concrete `branch*_parallelogram` and four `branch*_zsmul` theorems have
only their point/integer arguments. Four model-instance bridges discharge
the nonsingularity of the exact casted model coefficients using the earlier
verified discriminants. There is no remaining bounded-defect or hypothetical
pairing assumption in those concrete endpoints.

## Remaining formal boundary

The finite Gram identity is not yet the numerical lower bound
`H(sum_i m_i P_i)>=sum_i m_i^2/100`: the exact logarithm intervals, actual
finite-iterate point certificates and matrix positivity must still be linked
to these Lean objects. The strong rational-point local gcd bound, global
minimum height, full descent/saturation interpretations, elliptic-logarithm
analysis and complete residual computation likewise remain to be formalized
or replaced. Their separate written/exact k=6 proof is already complete.

These two modules add 30 explicit audited declarations, bringing the project
total to 253. All proof terms use ordinary kernel-replayed reasoning and
standard logical axioms. The exact replay and clean-checkout record is in
[VERIFICATION.md](VERIFICATION.md). No whole-problem award eligibility follows.
