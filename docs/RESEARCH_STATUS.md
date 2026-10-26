# Current research obligations

The [written proof and independent exact certificates](K6_THEOREM.md) now
establish the k=6 noncollision theorem for every n>=0 and m>=n+6.
The 2026-10-25 rank and saturation certificates remove the earlier dependence
on Magma completion flags. This is a mathematical/computational result;
no complete Lean k=6 endpoint has been proved. The unrestricted Erdős #677
remains unresolved and no whole-problem award claim is justified.

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
Lean. The 2026-10-25 addition also proves the universal integral dual-functional
distance argument and all 25 concrete lattice distances, including their
explicit rounded integer inputs and strict thresholds. See
[the exact Lean scope](../cas/global-bound/LEAN_LATTICE.md). The numerical Gram certificate connection, David's theorem, elliptic uniformization, logarithm
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

## Independent group completeness, 2026-10-25

The new [minimum-height and saturation proof](../cas/saturation/SMALL_HEIGHT.md)
proves global H(P)>1/10, bounds the index in the saturated hull below 80, and
excludes every possible prime divisor using complete finite-field certificates.
The [rank proof](../cas/descent/RANK_PROOF.md) independently certifies maximal
orders, sufficient class-group relations, Kummer support and global squareclass
dimension bounds. A separate local-3 rank-four witness closes the last branch.
Thus all four displayed triples generate E(Q). None of these conclusions
assumes a Magma rank, class-group or full-basis flag.

## Remaining fixed-length obligations

1. Develop a complete Lean endpoint for all n>=0 and m>=n+6. The current
   253 audited declarations cover specified reductions, certificate algebra,
   integer lattice distances, conditional rounding and an abstract saturation
   bridge, real quartic bounds and actual primitive coordinate-height limits.
   Numerical Gram certificate interpretation, and the analytic,
   descent and finite computation chain
   remains outside Lean and must be proved or replaced there.
2. Continue source/priority checks and address substantive external review.
   The completed independent group certificate is not an unfinished task to
   be repeated; any specific discovered error must be corrected publicly.
3. Pursue a uniform argument or counterexample for the unrestricted problem,
   rather than treating further finite lists of lengths as a full solution.

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

## Uniform structure follow-up, 2026-10-25 evening

The [two-factor argument](UNIFORM_STRUCTURE.md) strengthens the earlier Hall
observation: beyond an explicit k-dependent threshold, every genuine
collision's q>k ownership graph must contain two edge-disjoint perfect
matchings. It uses the paper's quadratic lift, an explicit polynomial root
bound excluding vanishing lifts, and exact cut products. This is written
mathematics, not a Lean endpoint or an all-length solution. Nonvanishing
alternating cycles remain uncontrolled; the abstract permitted growth pattern
is not an integer counterexample. No additional collision enumeration was run.

The [new Lean height layer](../cas/height-bounds/LEAN_DYNAMICS.md) now proves
real quartic bounds and unconditional canonical limits for all four actual
primitive coordinate maps, including H-h<5. At that checkpoint it did not
yet connect them to Mathlib's elliptic group law. The subsequent bridge below
closes that obligation. The evening pairing integration below also closes the
actual pairing input; the later numerical and certificate chain remains open.

The later [component/cycle argument](UNIFORM_CYCLES.md) adds explicit necessary
conditions: component sizes are multiples of the radical degree d, and for
d>=4 sufficiently large collisions require at least 2k+1 occupied packets.
Thus pure alternating cycle covers are excluded in that degree range; graphs
with additional branching remain the precise uniform obstruction. The proof
is written mathematics, with no collision enumeration or Lean endpoint.

## Actual elliptic heights and all-degree cycle exclusion, 2026-10-26

The [elliptic bridge](LEAN_ELLIPTIC_HEIGHT.md) removes the group-identification
obligation: the actual Mathlib point group, projective x-height and every
primitive-coordinate iterate are linked in Lean. All four curves now have
unconditional group-height convergence and H-h<5 endpoints, including O.
A separate generic theorem derives exact quadraticity and a biadditive pairing
from a uniform bounded naive parallelogram defect. Proving that specific
input on the four curves remains unfinished; it is not silently assumed.

The [low-degree continuation](UNIFORM_LOW_DEGREE.md) removes the d>=4
restriction from the pure-cycle exclusion. Exact normalized coefficient
support excludes d=2 and leaves just two d=3 branches; five finite-field
witnesses exclude their cycle products. Thus, for every k>=2 beyond the
existing explicit threshold, a hypothetical collision requires at least
2k+1 occupied packets. Additional branching remains unresolved. This written
structural theorem is not Lean-formalized and does not solve the original
problem or change award eligibility.

The [quantitative branching bound](UNIFORM_BRANCHING.md) also proves
`n<=Ncycle*W^(2d)` for the product W of packets outside any chosen spanning
two-factor, with no new height or CAS assumption. Consequently bounded extra
packets cannot sustain arbitrarily large starts at fixed k. Unbounded W
remains possible under these necessary conditions; no global contradiction
or valid collision has been obtained.

## Actual pairing and local branching, 2026-10-26 evening

The [pairing integration](LEAN_PAIRING.md) proves the actual-curve bounded
parallelogram input, symmetric biadditive canonical pairing, integer
quadraticity, nonnegativity and finite Gram expansion in the pinned project.
The previous pairing obligation is closed. Michael Stoll's earlier general
Mathlib main formalizations are explicitly credited; this is a specialized
fixed-version integration and concrete canonical-height application.
The numerical interval/matrix certificates and later k=6 chain remain
unconnected to their actual Lean objects.

The [local branching theorem](UNIFORM_LOCAL_BRANCHING.md) proves
`n<=Nvertex*V^(2d)` at every vertex after removing any two incident packets.
Beyond an explicit k-dependent threshold every vertex has degree at least
three, hence at least 3k occupied packets are necessary. No perfect matching
hypothesis is needed. Unbounded local complements and minimum-degree-three
graphs remain unresolved. This written result is not Lean-formalized and
does not settle arbitrary k or change whole-problem eligibility.
