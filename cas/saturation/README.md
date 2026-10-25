# Independent saturation certificates (25 October 2026)

This directory supplies exact certificates and a human proof that each of the
four specified rank-three subgroups is completely saturated in `E(Q)`. It
combines the finite-prime reduction argument below with the global minimum
height and bounded-index proof in [SMALL_HEIGHT.md](SMALL_HEIGHT.md).
**It does not prove a rank upper bound.** Thus additional independent
rational points, and consequently full rational-group coverage, remain
unexcluded without a separate rank argument. The height/reduction arguments
are not complete Lean theorems. No Magma output is used by these programs.

The portable, read-only replay command from the repository root is:

```sh
python3 cas/saturation/verify_all.py
```

It runs both independent checkers and matches the curve models, three
rational generators, and input hashes against the existing height certificates.
All scripts use only the Python standard library and require assertions.
The sections below document the finite-prime part on its own.

For each of the four curves and three displayed points already used in
`cas/global-bound`, let `G` denote their integer span in `E(Q)`.
The exact finite-field data, together with the standard good-reduction group
homomorphism, prove:

1. `E(Q)` is torsion-free.
2. For every prime `ell <= 101`, if `ell*P` belongs to `G`, then `P` belongs to `G`.

The primes are exactly
`2,3,5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61,67,71,73,79,83,89,97,101`.
The four bases and curve coefficients are fixed literally in both programs.
No assertion here depends on interpreting a CAS flag as a proof.

## Torsion certificate

For a good prime `p`, rational torsion killed by a prime `ell != p` injects
into `E(F_p)`. Therefore any prime divisor of the order of a rational torsion
point divides `p * #E(F_p)`. Two such augmented orders with gcd one exclude
all nonzero rational torsion. This uses only prime-to-characteristic
injectivity; it does not silently assume injectivity for the p-primary part.

| pair | good primes p | independently counted orders N_p | gcd(p N_p) |
|---|---|---|---|
| (1,2) | 11,13 | 15,19 | 1 |
| (1,5) | 7,11 | 9,16 | 1 |
| (1,10) | 7,19 | 9,20 | 1 |
| (2,5) | 13,37 | 14,33 | 1 |

Both programs check primality and nonzero cubic discriminant modulo each
prime; the elliptic discriminant is 16 times that cubic discriminant, and
all primes here exceed three. The two torsion point counts are enumerations,
not Hasse-bound estimates.

## Prime saturation certificate

Fix one of the listed primes `ell`. For each of three auxiliary good primes
`p != ell`, the certificate gives a point generating the **whole** finite
cyclic group `E(F_p)`, whose order `N` is divisible by `ell`. The map taking
the index of a point with respect to this generator, modulo `ell`, is a
well-defined group homomorphism `E(F_p) -> F_ell`: changing the integer index
by `N` does not change it modulo `ell`. Compose it with good reduction on
`E(Q)`. The images of the three rational generators give one row of a
3-by-3 matrix over `F_ell`. Its recorded integer determinant is nonzero
modulo `ell`.

Suppose `ell*P = n1*P1+n2*P2+n3*P3`. Applying the three homomorphisms kills
the left side, so the invertible matrix forces all `ni` to be divisible by
`ell`. Set `R=P-sum (ni/ell)*Pi`. Then `ell*R=0`; the preceding torsion
certificate gives `R=0`, proving `P in G`. This argument does not require a
rank upper bound. The previously certified positive height matrix separately
proves that the three generators are independent.

The 104 saturation matrices use 294 distinct finite cyclic groups across
all four curves. Largest auxiliary primes are respectively 2963, 2707,
4211, and 6491. These finite-field data alone certify only the stated 26 primes. The separate global-height/index proof in `SMALL_HEIGHT.md` upgrades this to complete saturation; higher rank remains unexcluded.

## Independent exact replay

From the repository root:

```sh
python3 cas/saturation/certify_finite_saturation.py \
  --max-ell 101 --max-auxiliary 20000 \
  --output cas/saturation/finite_saturation.json
python3 cas/saturation/verify_finite_saturation.py \
  cas/saturation/finite_saturation.json \
  --output cas/saturation/independent_verification.json
```

Both actually ran and passed on 25 October 2026, using Python 3.14.6 and only
the standard library. Keep assertions enabled. The discovery program counts
points by a table of square roots, searches for a generator and verifies its
entire cycle. The independent verifier imports none of its code: it counts
points by Euler's criterion, replays translation by the proposed generator
using the third intersection of a line with the cubic, checks every visited
point and no duplicates, and verifies cycle length equals the independently
counted cardinality. It checks the exact generator indices of each basis
point and determinants by the signed-permutation formula. All arithmetic
is integer or `Fraction`; no floating point is used.

Certificate SHA256:
`b8ccc420ebbd65173a8631bb344c08f51169c5adfa98223c41c6a4d5fffa1dd6`.
Independent verifier SHA256:
`4c07f8e84949dd202a569d52f4ab288247e71850426988c8e3273408b516d58e`.
The generator writes a Python version string, so its byte hash is tied to
that runtime, while the arithmetic certificates are portable.

The geometric/group-theoretic interpretation is a human proof. These files
are not yet Lean certificates for actual elliptic-curve reductions.

## Sources and remaining route

The reduction homomorphism and prime-to-characteristic torsion injectivity
are standard; see J. S. Milne, *Elliptic Curves*, second edition, chapter II
section 4 and Corollary 4.2(b), printed pages 62–64:
<https://www.jmilne.org/math/Books/EC2.pdf>.

A rigorous route to full generation is an independently certified rank upper
bound three, followed by an upper bound for the index of `G`. A **global**
positive lower bound for canonical height on all nonzero rational points,
combined with the known subgroup regulator, would supply that index bound.
The current height inequality `H(sum mi Pi) >= (sum mi^2)/100` applies only
to `G` and cannot be reused as a lower bound on all of `E(Q)`.

Cremona–Siksek give an algorithm for a global minimum height in *Computing a
Lower Bound for the Canonical Height on Elliptic Curves over Q*, ANTS VII
(2006), pp.275–286, author PDF:
<https://johncremona.github.io/papers/HeightLB.pdf>.
Its real-circle method first treats the subgroup of points having good
reduction at every place; passing to all rational points requires the
Tamagawa-component multiplier. Omitting that multiplier is invalid.

Subsequent work in `SMALL_HEIGHT.md` and its two exact programs establishes the missing global minimum-height/index assertion and, combined with these finite-prime certificates, complete saturation. The rank upper bound remains unproved independently. The finite-prime result documented above remains valid on its own.
