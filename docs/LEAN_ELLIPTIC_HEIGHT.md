# Actual elliptic doubling and the remaining quadraticity input

Author: MaxwellLaw. Checkpoint: 26 October 2026 (Asia/Shanghai).
The author, MaxwellLaw, used AI as an assistive tool.

The subsequent [evening pairing integration](LEAN_PAIRING.md) has now proved
the actual-curve bounded-defect premise and its concrete canonical pairing
consequences. The morning checkpoint below is retained as history.

This morning checkpoint connects the previously formalized primitive-coordinate map
to Mathlib's actual nonsingular elliptic point group. It also formalizes the
standard implication from a bounded naive parallelogram error to an exact
canonical quadratic height. The latter error estimate on the four actual
curves remains a separate obligation. There is still no complete Lean k=6
endpoint, and the all-length problem remains unresolved.

## The actual point group

`LcmSix/EllipticDuplication.lean` uses the exact model
`y^2=x^3+a*x^2+b*x+c` and Mathlib's `WeierstrassCurve.Affine.Point` group.
`quartic_xRep_double` proves that the two quartics F,G applied to `P.xRep`
are a nonzero scalar multiple of `(P+P).xRep`. The proof includes the point
at infinity, finite points with y=0 doubled to infinity, and the ordinary
tangent case. It uses the actual Mathlib addition formulas; a proposed
coordinate operation is not assumed to be the group operation.

`step_represents` then identifies the existing gcd-normalized integer map
with that group doubling for every primitive representative. Division is by
the actual proved positive gcd. `primitiveRep` supplies an unconditional
representative of every point: (1,0) at infinity and the reduced numerator
and positive denominator of the affine x-coordinate otherwise.
`height_eq_of_represents` identifies its log-max height with Mathlib's
projective logarithmic height, using invariance under nonzero rational
scaling. Compatibility continues through every iterate.

`canonicalHeight` is defined directly from the actual group-doubling orbit.
`canonicalHeight_eq` proves equality with the earlier coordinate limit;
`tendsto_canonicalHeight`, `canonicalHeight_double` and
`canonicalHeight_enclosure` transfer convergence, scaling and finite-iterate
error bounds. The four `branch*_group_converges` endpoints use the actual
`(2^n : Nat) • P`, and `branch*_group_height_error` proves H(P)-h(P)<5.
They take only an actual point P; no representation, convergence, model
correctness or group-compatibility premise remains. Four exact nonzero
discriminants also supply `IsElliptic` instances for the displayed curves.

The implementation builds on Mathlib's affine point and projective-height
APIs, including the elliptic group work of David Kurniadi Angdinata. Their
original attribution and licenses are unchanged. The mathematical tangent
and height formulas are standard; no discovery priority is claimed.

## What the conditional quadraticity theorem proves

For any abelian group A and real-valued function h, the explicit premise in
`LcmSix/CanonicalQuadratic.lean` is

```
exists C, for every x,y,
  |h(x+y)+h(x-y)-2*h(x)-2*h(y)| <= C.
```

Fixing such a C, the module derives the bounded doubling defect and proves
that `H(x)=lim_n 4^(-n) h([2^n]x)` exists. Dividing the displayed error by
4^n and taking those proved limits yields the exact parallelogram law.
No convergence or exact quadraticity is an assumption.

Purely algebraic lemmas then prove that

`B(x,y)=(H(x+y)-H(x-y))/4`

is symmetric and additive in each argument, with `B(x,x)=H(x)`.
`bilinear` constructs an actual `A ->+ A ->+ Real`, and `map_zsmul` proves
`H([n]x)=n^2 H(x)` for every integer n, including zero and negative values.
The normalization is the x-height convention used throughout this project.

This is a formalization of standard canonical-height theory; see
[Milne, Elliptic Curves](https://www.jmilne.org/math/Books/EC2.pdf),
Chapter IV, Proposition 4.9 and Lemma 4.11. It does not assert that every
naive function satisfies the explicit bounded-error premise. In particular,
this checkpoint has not yet discharged that premise for the four curves.

## Remaining formal obligations

The missing actual-curve parallelogram error estimate is now isolated from
the proved limit and polarization steps. Mathlib's `Affine/AddSubMap.lean`
by Michael Stoll contains polynomial and coefficient identities, but its
header still lists the identification with `(P+Q,P-Q)` as a TODO in the
pinned version. That identity must be proved before using this route.

The strong rational-point local-square gcd bounds, the independent descent
and saturation interpretations, the elliptic-logarithm lower bound and
integration, and the complete residual calculation still require Lean
proofs or a different complete route. Their written mathematical and exact
certificate proofs were already completed; this checkpoint does not reopen
them as mathematical gaps. It advances formalization only.

Actual replay commands, cache scope and axiom reports are recorded in
[VERIFICATION.md](VERIFICATION.md). The code uses ordinary kernel-replayed
proofs and the standard logical axioms, with no custom mathematical axiom,
unproved key assumption hidden in a concrete endpoint, or CAS oracle.
