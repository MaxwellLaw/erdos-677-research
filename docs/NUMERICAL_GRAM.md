# Kernel-checked numerical heights of the actual point triples

Author: MaxwellLaw. Checkpoint: 27 October 2026, morning.
The author, MaxwellLaw, used AI as an assistive tool.

For each of the four actual rational elliptic curves, Lean now proves

```
forall m : Fin 3 -> Int,
  (sum_i (m_i : Real)^2)/100 <= H(sum_i m_i * P_i).
```

The operation on the right is actual integer scalar multiplication and
addition in Mathlib's rational point group. H is the existing x-normalized
canonical height, defined by the proved group-doubling limit. All orbit,
primitivity, real logarithm, rounding and matrix premises have been discharged.
The four `HeightLowerBound.branch*_relation_trivial` theorems also prove
that an integer relation among the three actual points has every coefficient
zero. This is independence and a lower bound on the displayed generated
subgroups. **It does not formalize full-group generation, the complete k=6
endpoint, or the all-length original problem.**

## Exact endpoints and inputs

The endpoints in [HeightLowerBound.lean](../LcmSix/HeightLowerBound.lean) are
`branch1_2_lower`, `branch1_5_lower`, `branch1_10_lower`, and
`branch2_5_lower`. Each has only `m : Fin 3 -> Int` as its argument.
The matching `branch*_relation_trivial` theorems have the actual integer
relation as an explicit hypothesis and conclude `forall i, m i = 0`.

The actual models and point triples are unchanged from the earlier exact
certificate:

| Branch | Curve | P1 | P2 | P3 |
| --- | --- | --- | --- | --- |
| (1,2) | y²=x³−x²−65x+261 | (5,6) | (13,38) | (−7,18) |
| (1,5) | y²=x³−x²−408x+6912 | (12,−60) | (−4,92) | (78,−666) |
| (1,10) | y²=x³+x²−1633x+97763 | (221/4,3387/8) | (14,279) | (43,330) |
| (2,5) | y²=x³+x²−1633x+32963 | (23,−90) | (17,−102) | (−1,186) |

`HeightPoints.lean` defines all twelve points and all twelve pairwise sum
points, proves their curve equations and nonsingularity, and identifies the
sums with actual group addition. `HeightGram.Branch*.basis` is the explicit
three-entry function used in the endpoint; its name does not assert that it
is already a formalized basis of the entire rational-point group.

## Finite projective certificates

`HeightOrbits.lean` uses an integer pair representing the actual projective
x-coordinate, with an explicit nonzero rational scaling factor. Its generic
`raw_step` proves that checked integer identities

```
F(p,q)=d*p', G(p,q)=d*q', d != 0
```

transport that representation to the actual doubled point. The quotient d
may have either sign. No claim that it is the gcd is required at intermediate
steps, and no division or normalization convention is silently changed.

All 24 seven-step chains are explicit data checked by ordinary kernel
`decide`: 168 F/G pairs and nonzero quotient conditions. Each final pair has
an explicit integer Bezout witness proving primitivity; its positive maximum
B is checked. The final `height7` theorem gives

```
naiveHeight([128]P) = log B
```

for the actual point and its actual group orbit. The largest final coordinate
has 221662 bits. Intermediate projective pairs need not be primitive, but
final primitivity is essential to this exact height formula and is proved.
The exporter reproduces the original saved final coordinates exactly.

## Strict real logarithm bounds

`LogBounds.lean` uses the pinned Mathlib results
`Real.sum_range_le_log_div` and `Real.log_div_le_sum_range_add`.
For z in [0,1), with T=40, these give twice the finite atanh series as a lower
bound and the additional remainder

```
2*z^(2*T+1)/(1-z²)
```

as an upper bound. The proof does not insert the smaller remainder's extra
factor `(2*T+1)` from the original discovery script.

`LogCertificates.lean` verifies 60 rational mantissa enclosures. The
intermediate endpoints use outward rounding to 80 binary places. Binary
scaling then produces 32 real logarithm enclosures, each outward rounded to
48 places: 24 final coordinate maxima and the four C and D constants.
Large binary brackets are verified by natural-number cross products with
positive denominators, then proved to imply the rational inequalities.
They do not require trusting a floating-point logarithm or Python rounding.

The explicit `exponentiation.threshold=300000` setting permits ordinary
kernel evaluation of the recorded powers of two; the largest exponent is
221661. This changes a computation resource guard, not the axiom or evaluator
trust boundary. No `native_decide`, external numerical axiom or CAS assertion
is used.

## From finite heights to canonical heights

The already proved actual-group tail has lower constant `log(32R)` and
upper constant `log C`. All four exact models satisfy

```
32*gmax < 32R < D.
```

Thus monotonicity of the real logarithm permits the conservative lower tail
with D used by the old certificate. `HeightEnclosure.from_seven_steps` proves
that inference with the exact factor `4^7=16384`.
`HeightIntervals.lean` discharges every premise and proves all 24 original
closed canonical-height intervals for the actual points. The old intervals
and saved coordinate data are unchanged. Their historical JSON status text
is retained as part of the fixed data; this new Lean consumer supplies the
previously missing verification.

The separate sharper rational-point bound involving gmax is still needed
for the global minimum-height argument. It is not an assumption of these
new numerical Gram endpoints and has not been formalized by this addition.

## Matrix and actual group connection

`GramBounds.lean` proves the symmetric interval error bound using
`2*abs(x*y)<=x²+y²`. `GramCertificates.lean` checks four explicit rational
LDL factorizations by polynomial identities and positive diagonal entries.
The resulting quadratic forms are bounded below by sums of nonnegative
squares; no numerical eigenvalue or unproved linear algebra assertion is used.

`HeightGram.lean` connects those six-entry certificates to the actual
canonical pairing. The already proved parallelogram law identifies
`(H(P+Q)-H(P-Q))/4` with `(H(P+Q)-H(P)-H(Q))/2`.
The finite actual group Gram expansion then gives the three-point form.
`HeightLowerBound.lean` supplies all six actual intervals in each branch,
removing every numerical premise. H(0)=0 and positivity of squares yield
the four integer-relation consequences.

## Attribution, replay and remaining scope

This formalizes the existing exact numerical certificates and standard
height/interval mathematics. The actual group and projective height APIs,
Stoll's earlier general parallelogram formalizations, and the standard
canonical-height theory retain the attribution in [LEAN_PAIRING.md](LEAN_PAIRING.md).
The real logarithm lemmas come from Mathlib's logarithm development credited
to Chris Hughes, Abhimanyu Pallavi Sudhir, Jean Lo and Calle Sönne. Point and
certificate provenance remains in [CAS.md](../cas/CAS.md) and the earlier
[height note](../cas/height-bounds/README.md). No first-formalization claim
is made.

The ten modules add 241 explicit audited declarations, for 494 in total
and 31 project modules. From the pinned project checkout:

```sh
lake --wfail build
python3 scripts/check_axioms.py
lake env leanchecker -v LcmSix
python3 scripts/export_height_orbits.py --check
python3 scripts/export_log_certificates.py
python3 scripts/export_height_intervals.py
python3 scripts/export_gram_certificates.py
```

The exporters are untrusted and check correspondence to the fixed original
JSON; the generated Lean source contains proofs of every mathematical
obligation. Replay and clean-checkout evidence, including dependency-cache
reuse, are recorded in [VERIFICATION.md](VERIFICATION.md).

The independent written/exact k=6 proof remains completed. Its remaining Lean
layers include the stronger local gcd/minimum-height argument, number-field
and descent interpretation, full saturation, elliptic integrals and effective
analytic bounds, and the complete residual exclusion. Arbitrary k remains
unresolved, with the previously documented unbounded transport branching.
No whole-problem awards PR or claim is justified by this fixed-length
formalization checkpoint.
