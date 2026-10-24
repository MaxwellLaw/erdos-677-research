# Current research obligations

The analytic argument and exact arithmetic now exclude every admissible
length-six candidate whose elliptic image belongs to one of the four explicit
rank-three generated subgroups. Using the recorded external Magma full-basis
flags gives a **CAS-supported computational k=6 noncollision corollary**. No
independently exported descent/saturation certificate has replaced that CAS
step, and no Lean k=6 endpoint has been proved. The unrestricted Erdős #677
remains open; this result does not justify an original-problem award claim.

## Completed fixed-length chain

The four-curve equivalence is kernel-checked, including exact carry filters.
The rational maps and their target-domain exceptions are checked exactly.
The height stage gives `H-h<5` and
`H(sum m_i P_i)>=sum m_i²/100`. David's theorem, with the actual degree-three
point Q0 and the correct height/differential normalization, gives
`max|m_i|<10^100`. Certified real-logarithm intervals and exact inhomogeneous
lattice-distance certificates reduce this to the closed bounds 60,60,62,64.
The complete residual enumeration covers 7,642,936 coefficient triples and
leaves no disjoint odd-square candidate. The three positive odd-square pairs
that survive the square tests have interval gaps 2,1,1 and are overlapping.

The integer Bézout identities, gcd bounds and coefficient sums are proved in
Lean. Canonical heights, David's theorem, elliptic uniformization, logarithm
integration and the interpretation of the finite-field sieve remain human
mathematics with exact Python certificates. The exported lattice verifier
checks unimodularity, inverse matrices, rounding cells and rational distance
bounds; it does not assume that an external LLL routine succeeded merely from
its return status.

See [the complete scoped statement](../cas/global-bound/README.md),
[initial bound](../cas/global-bound/INITIAL_BOUND.md),
[lattice argument](../cas/global-bound/LATTICE.md), and
[residual enumeration](../cas/global-bound/ENUMERATION.md).
Reproduce the recorded arithmetic with
`python3 scripts/verify_global_bound.py` from the repository root.
Actual execution records and the Lean boundary are in
[VERIFICATION.md](VERIFICATION.md).

## Remaining fixed-length obligations

1. Export and independently check the full Mordell–Weil generation evidence,
   including rank and saturation, instead of relying solely on Magma's
   `rankproved` and `fullproved` flags.
2. Develop a Lean endpoint for all n>=0 and m>=n+6. This requires formalizing
   the analytic completeness argument or replacing it with a different
   kernel-checkable complete method, as well as checking the finite arithmetic.
   A fast Python replay is not a Lean proof.
3. Continue source and priority checks and address substantive external review.
   A mathematical or implementation error must update the same public record.

## The all-length problem

A uniform prime-power ownership route was checked. Write d=m-n. Every maximal
prime power of a common LCM divides some d+j-i with 1<=i,j<=k, hence

`M_k(n) | lcm(d-k+1,...,d+k-1)`.

This is the paper's existing bridge restriction, not a new theorem. Together
with `P_k(n)/M_k(n) | (k-1)!` it gives only

`(n+1)^k <= (k-1)! (d+k-1)^(2k-1)`.

Along a fixed length-six product-ratio branch, d is asymptotic to
`((b/a)^(1/6)-1)n`. The inequality permits arbitrarily large scale; losing the
position information of each prime-power factor prevents a global bound.
A useful next structural route must retain that position information or
produce an actual disjoint equal-length collision. Extending a finite list
of fixed lengths alone cannot settle the unrestricted quantifier.

Finite congruence tests on the four product equations plus carry filters also
have positive disjoint representatives for every modulus, as proved in Lean.
This does not obstruct the finite-field sieves used after the global bound,
and it does not rule out congruences combined with descent or additional
arithmetic information. No uniform all-k proof or valid counterexample has
been obtained.
