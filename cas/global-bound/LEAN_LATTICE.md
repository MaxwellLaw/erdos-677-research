# Kernel-checked integer lattice distances

Author: MaxwellLaw. Verification date: 2026-10-25 (Asia/Shanghai).

This checkpoint formalizes the universal distance argument and all 25 concrete
integer distance certificates from `lattice_reduction.json`. It does not
formalize real logarithm enclosures, canonical heights, David's theorem,
Mordell–Weil generation, residual elliptic-point enumeration, or a k=6 endpoint.

## Integral dual certificate

The original column lattice has vectors

`v=(m1,m2,m3,a1*m1+a2*m2+a3*m3+a0*m0)`,

for arbitrary integers m1,m2,m3,m0, and target `t=(0,0,0,aQ)`.
Let an integer row w and positive integer d satisfy

`w1+w4*a1=d*q1`, `w2+w4*a2=d*q2`, `w3+w4*a3=d*q3`,
`w4*a0=d*q4`, and `w4*aQ=d*qt+r`.

For every such v, the functional is exactly

`w·(v-t)=d*(q1*m1+q2*m2+q3*m3+q4*m0-qt)-r`.

If `0<=delta<=r` and `delta<=d-r`, its absolute value is at least delta:
for the integer in parentheses at most zero use the distance to r; otherwise
it is at least one and the distance is at least d-r. Squaring and the
four-dimensional Cauchy–Schwarz identity give

`delta² <= (w1²+w2²+w3²+w4²)*||v-t||²`.

Thus the checked strict inequality

`(w1²+w2²+w3²+w4²)*T < delta²`

proves `T < ||v-t||²` for **all integer coefficient quadruples**. The proof
uses no floating arithmetic, inverse-matrix assertion, unimodularity result,
or asserted LLL quality. Those tools only discover an appropriate integer row.

The generic theorem `Certificate.last_coordinate_large` also proves that if
`T=3*B²+H²`, `B,H>=0`, and `|mi|<=B` for i=1,2,3, then

`H < |a1*m1+a2*m2+a3*m3+a0*m0-aQ|`.

Its conclusion is about the rounded integer linear form. The subsequent theorem `Certificate.real_linear_form_large` in
[`LatticeRounding.lean`](../../LcmSix/LatticeRounding.lean) also proves the
conditional transfer to real linear forms. Its hypotheses are the five explicit
rounding errors at most 1/2, the three coefficient bounds,
`|m0|<=3*B+1`, and `K>=0`; its threshold is
`T=3*B²+(3*B+1+K)²`. It concludes
`K < |C*(m1*u1+m2*u2+m3*u3+m0*omega-uQ)|`.
The helper `rounding_error_bound` proves the total error at most `3*B+1`,
including the period and target terms. The theorem uses `|CL|`, so it needs
no hidden assumption `C>0`. Actual elliptic-logarithm enclosures and the
coefficient/period bound still have to be supplied from the human argument.

## Concrete evidence and correspondence

[`LatticeDistance.lean`](../../LcmSix/LatticeDistance.lean) proves the residue
lemma, Cauchy–Schwarz inequality, generic distance theorem and last-coordinate
consequence. [`LatticeCertificates.lean`](../../LcmSix/LatticeCertificates.lean)
contains 25 explicit integer data structures, 25 validity theorems and 25
universal distance theorems. They use ordinary `norm_num` proofs replayed by
Lean's kernel. The largest supplied integer has 421 decimal digits.

The branch and zero-based step are part of every name, for example
`LcmSix.LatticeDistance.step_1_2_0_distance`. The concrete theorem expands the
original rounded logs, period, target and strict squared-radius threshold;
there is no assumption that its certificate is valid.

[`export_lattice_certificates.py`](../../scripts/export_lattice_certificates.py)
clears denominators of the selected inverse row from the old certificate.
It checks the integral dual identities, the target residue and equality
`delta²/sum(wi²) = distance_squared_lower`. The threshold is exactly
`3*B0²+(3*B0+1+10^q)²`, with the existing input bound B0 and exponent q.
It compares both generated artifacts byte-for-byte with the saved files and
records the original lattice JSON SHA256 in `dual_certificates.json`.

Run from the repository root:

```sh
lake --wfail build
python3 scripts/check_axioms.py
lake env leanchecker -v LcmSix
python3 scripts/export_lattice_certificates.py
```

The exporter is an untrusted witness producer and correspondence check;
the 25 validity/distance statements are checked by Lean independently of its
execution. Use `--write` only to regenerate the explicit source and JSON.
Actual build, axiom and clean-checkout records are in
[VERIFICATION.md](../../docs/VERIFICATION.md). Neither this formalization nor
the previous computational fixed-length corollary resolves the all-k problem.
