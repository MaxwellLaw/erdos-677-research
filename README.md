# Erdős 677: length-six proof and partial Lean formalization

**Status: the written proof and independently replayable exact certificates establish the k = 6 noncollision theorem. Rank and complete-group generation are now independently certified; Magma completion flags are no longer proof assumptions.** There is no complete Lean k = 6 endpoint. The original all-length Erdős Problem 677 remains unresolved. JSP-000550 denotes Erdős Problem 677, not Erdős Problem 550. See [the precise theorem and complete proof chain](docs/K6_THEOREM.md).

Author and Lean formalization author: MaxwellLaw. The author, MaxwellLaw, used AI as an assistive tool.

For natural numbers n,k, define M(n,k) = lcm(n+1,...,n+k). The original question asks whether M(n,k) differs from M(m,k) whenever k > 0 and m >= n+k. Our definition uses exactly `Finset.Ioc n (n+k)`; it includes n=0 and adjacent disjoint intervals m=n+k.

## Checked results

- `LcmSix.product_six` proves, for every natural n, `product n 6 = carry n * M n 6`, where `carry n = 12 * (if n%4<2 then 1 else 2) * (if n%5=4 then 5 else 1)`.
- `LcmSix.collision_iff_four_curves` proves a **two-way equivalence** between a length-six collision in the original disjoint range and four explicitly defined curve branches. Each branch includes its exact carry constraint. For X=2n+7, Y=2m+7, Phi(T)=(T-1)(T-9)(T-25), the equations are a Phi(Y²)=b Phi(X²) with (a,b) in {(1,2),(1,5),(1,10),(2,5)}. This theorem does not prove those branches empty.
- `LcmSix.no_collision_of_carry_le` excludes all n<m whose later carry factor is at most the earlier one. This is an infinite subfamily, not all starts.
- `LcmSixGcd.common_divisor_square_dvd` proves that any common divisor d of X,Y satisfies d² | 225(b-a) under the curve equation.
- `LcmSix.CarryGcd` specializes the known gcd restrictions with the exact carry filters: the center gcd divides 15,3,9,3 and the slope gcd divides 15,12,81,9 in the respective four branches. These bounds do not bound the interval starts.
- `HeightCertificates` proves the integer Bézout identities for all four duplication-polynomial pairs, their common-divisor bounds at primitive integer coordinates, and the exact coefficient sums C,D. The interpretation as elliptic-curve duplication and the resulting analytic height bounds are separate human proofs.
- `LcmSix.LatticeDistance` proves the universal integer dual-functional distance argument and all 25 explicit squared-distance bounds used in the global reduction. The rounded integer linear forms and thresholds are expanded in the concrete theorem types. The generic rounding-error transfer to real linear forms is also kernel checked; actual elliptic-logarithm enclosures remain a separate human argument.
- The new real duplication and primitive-dynamics modules prove all four global quartic lower bounds, actual gcd-normalized coordinate-height convergence, finite-iterate enclosures, uniqueness and the strict bound `H-h<5`. These are unconditional results on primitive integer pairs; elliptic-group identification and quadraticity remain separate obligations. See [the exact scope](cas/height-bounds/LEAN_DYNAMICS.md).
- `LcmSix.ModularObstruction` proves that specified product-congruence and carry sieves have positive disjoint surviving representatives for every positive modulus. These are congruence witnesses, **not integer-product equalities or LCM counterexamples**.

The separate [rigorous height calculation](cas/height-bounds/README.md) establishes `H(P)-h(x(P))<5` on all four elliptic curves and `H(sum m_i P_i)>=sum m_i²/100` on each displayed generated subgroup, using exact rational intervals and a human canonical-height argument. Here H is the x-normalized canonical height. The [global coefficient bound and residual certificate](cas/global-bound/README.md) now combine these estimates with David's elliptic-logarithm theorem, certified real logarithms and exact lattice-distance bounds. They reduce the four coefficient boxes to closed bounds 60,60,62,64 and exhaust all 7,642,936 triples. No admissible disjoint odd-square pair remains. The [independent rank and generation certificate](cas/descent/RANK_PROOF.md) now proves coverage of the entire rational-point group. Its number-field, height and finite-field interpretation, and the analytic/enumeration layers, remain outside Lean.

The product/LCM periodicity is prior work of Farhi–Kane; the four-coefficient reduction and centered gcd ideas build on Danesh–Bianchetti. The contribution here includes the checked reductions, integrality diagnostics, explicit analytic constants, exact lattice-distance certificates and complete residual enumeration. These layers are documented with separate trust boundaries. No worldwide mathematical or formalization priority is claimed.

## Reproduce

Lean: `leanprover/lean4:v4.33.1`, compiler commit `819816b2e0a3bf405af45ae5c7af2491d8f5bee6`.

Mathlib: `0df444a360eaa60ab8c11dca51a86af692955474`, with all transitive revisions fixed in `lake-manifest.json`. These match the inspected Formal Conjectures revision.

```sh
lake exe cache get
lake --wfail build
python3 scripts/check_axioms.py
python3 scripts/export_lattice_certificates.py
python3 scripts/export_duplication_certificates.py
lake env leanchecker -v LcmSix
python3 scripts/verify_reduction.py
python3 scripts/verify_heights.py
python3 scripts/verify_global_bound.py
python3 cas/saturation/verify_all.py
python3 cas/descent/verify_all.py
```

The Lean proofs use ordinary kernel-replayed tactics. They contain no sorry, admit, custom mathematical axioms, or native_decide. Externally discovered polynomial coefficients and integral lattice witnesses are supplied as explicit data and their obligations are proved by the kernel; no CAS assertion is accepted as an axiom. The printed dependencies are standard Lean logical axioms only. Mathlib dependency binaries may come from its public cache; all project modules are rebuilt for the clean-checkout test. The reduction sanity check is finite. The height replay verifies exact arithmetic certificates whose global implications use the documented height theory. Elliptic-group identification and quadraticity remain outside Lean; the elementary limit and actual coordinate dynamics are now formalized separately. The global-bound replay checks the recorded height parameters, real-logarithm intervals, initial-bound constants, lattice reductions and complete coefficient boxes. Its mathematical interpretation also uses the documented analytic and reduction theorems. Magma rank and full-basis results are retained as historical cross-checks; independent certificates now replace their role in the mathematical proof. None is a Lean assumption.

## Research and submission record

- [The precise k = 6 theorem and complete mathematical proof chain](docs/K6_THEOREM.md)
- [Original reduction audit](docs/MATHEMATICS.md)
- [Independent full-group certificate](cas/descent/RANK_PROOF.md)
- [Global minimum height and complete saturation](cas/saturation/SMALL_HEIGHT.md)
- [Fixed source versions and audit status](docs/SOURCES.md)
- [Prior submissions and current eligibility](docs/PRIOR_WORK.md)
- [Lean theorem-to-proof correspondence and actual validation](docs/VERIFICATION.md)
- [Curve calculations, exact maps and CAS trust boundary](cas/CAS.md)
- [Kernel-checked integer lattice distances](cas/global-bound/LEAN_LATTICE.md)
- [Global bounds, residual exhaustion and computational k = 6 corollary](cas/global-bound/README.md)
- [Rigorous height bounds and their trust boundary](cas/height-bounds/README.md)
- [Earlier period results and unverified literature hypotheses](cas/LITERATURE_SUPPLEMENT.md)
- [Direct Thue-substitution route and its obstruction](cas/thue-route/README.md)
- [Current research obligations](docs/RESEARCH_STATUS.md)
- [A uniform two-matching necessary condition, not an all-length solution](docs/UNIFORM_STRUCTURE.md)
- [Effective component resonance and pure-cycle exclusion](docs/UNIFORM_CYCLES.md)
- [Kernel-checked real bounds and canonical coordinate dynamics](cas/height-bounds/LEAN_DYNAMICS.md)

The current awards rules require a complete solution of the original problem. The computational fixed-length result and partial Lean formalization do not settle the all-length conjecture. No awards solution PR or whole-problem award claim is justified by this result. Remaining obligations include a complete Lean k = 6 endpoint, continued external review, and a separate argument or counterexample for arbitrary k.

License: Apache-2.0. Referenced third-party papers and proof repositories retain their own authorship and licenses; they are linked rather than vendored here.
