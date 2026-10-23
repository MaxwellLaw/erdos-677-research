# Erdős 677: verified length-six reductions

**Status: neither the full k = 6 noncollision theorem nor Erdős Problem 677 is solved here.** No valid disjoint equal-length collision is known from this work. JSP-000550 denotes Erdős Problem 677, not Erdős Problem 550.

Author and Lean formalization author: MaxwellLaw. The author, MaxwellLaw, used AI as an assistive tool.

For natural numbers n,k, define M(n,k) = lcm(n+1,...,n+k). The original question asks whether M(n,k) differs from M(m,k) whenever k > 0 and m >= n+k. Our definition uses exactly `Finset.Ioc n (n+k)`; it includes n=0 and adjacent disjoint intervals m=n+k.

## Checked results

- `LcmSix.product_six` proves, for every natural n, `product n 6 = carry n * M n 6`, where `carry n = 12 * (if n%4<2 then 1 else 2) * (if n%5=4 then 5 else 1)`.
- `LcmSix.collision_iff_four_curves` proves a **two-way equivalence** between a length-six collision in the original disjoint range and four explicitly defined curve branches. Each branch includes its exact carry constraint. For X=2n+7, Y=2m+7, Phi(T)=(T-1)(T-9)(T-25), the equations are a Phi(Y²)=b Phi(X²) with (a,b) in {(1,2),(1,5),(1,10),(2,5)}. This theorem does not prove those branches empty.
- `LcmSix.no_collision_of_carry_le` excludes all n<m whose later carry factor is at most the earlier one. This is an infinite subfamily, not all starts.
- `LcmSixGcd.common_divisor_square_dvd` proves that any common divisor d of X,Y satisfies d² | 225(b-a) under the curve equation.
- `LcmSix.CarryGcd` specializes the known gcd restrictions with the exact carry filters: the center gcd divides 15,3,9,3 and the slope gcd divides 15,12,81,9 in the respective four branches. These bounds do not bound the interval starts.
- `LcmSix.ModularObstruction` proves that specified product-congruence and carry sieves have positive disjoint surviving representatives for every positive modulus. These are congruence witnesses, **not integer-product equalities or LCM counterexamples**.

The coefficient reduction and centered gcd ideas build on the cited paper. The contribution here is the checked formalization, independent audit, explicit integrality diagnostics, and reproducible research material. No worldwide mathematical or formalization priority is claimed.

## Reproduce

Lean: `leanprover/lean4:v4.33.1`, compiler commit `819816b2e0a3bf405af45ae5c7af2491d8f5bee6`.

Mathlib: `0df444a360eaa60ab8c11dca51a86af692955474`, with all transitive revisions fixed in `lake-manifest.json`. These match the inspected Formal Conjectures revision.

```sh
lake exe cache get
lake --wfail build
python3 scripts/check_axioms.py
lake env leanchecker -v LcmSix
python3 scripts/verify_reduction.py
```

The Lean proofs use ordinary kernel-replayed tactics. They contain no sorry, admit, custom mathematical axioms, native_decide, or imported CAS certificates. The printed dependencies are standard Lean logical axioms only. Mathlib dependency binaries may come from its public cache; all project modules are rebuilt for the clean-checkout test. Python checks are finite sanity checks and are never used to assert noncollision for all starts. Magma calculations are separate exploratory evidence, not Lean assumptions.

## Research and submission record

- [Human mathematical proof and remaining gap](docs/MATHEMATICS.md)
- [Fixed source versions and audit status](docs/SOURCES.md)
- [Prior submissions and current eligibility](docs/PRIOR_WORK.md)
- [Lean theorem-to-proof correspondence and actual validation](docs/VERIFICATION.md)
- [Curve calculations and the next completeness obligation](cas/CAS.md)

The current awards rules require a complete solution of the original problem. This repository is a partial formalization, so it is not submitted as an original-problem solution and does not support a whole-problem award claim. Complete determination of admissible points on the four branches remains necessary to finish k=6; proving k=6 alone would still not settle the all-length conjecture.

License: Apache-2.0. Referenced third-party papers and proof repositories retain their own authorship and licenses; they are linked rather than vendored here.
