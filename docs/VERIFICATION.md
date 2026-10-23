# Statement correspondence and actual verification

This document verifies the auxiliary results in this repository. **There is no theorem proving all k=6 starts collision-free, and no theorem resolving all lengths.**

## Mathematical steps and Lean declarations

| Human step | Lean declaration | Exact scope |
| --- | --- | --- |
| Original positive interval | `LcmSix.M` in `LcmSix/Core.lean` | `(Finset.Ioc n (n+k)).lcm id`, for natural n,k; n=0 allowed. |
| Recursive/finite-set agreement | `LcmSix.window_eq_M` | All n,k. |
| Product versus LCM | `LcmSix.product_eq_defect_mul_window`, `LcmSix.product_six` | General recurrence, then exact length-six factor for every n. |
| Exhaustive coefficient ratios | `LcmSix.collision_iff_product_branches` | All n<m; exact carry equation is included in each branch. |
| Original disjoint-range reduction | `LcmSix.collision_iff_four_curves` | All natural n,m with n+6<=m; equivalence, not branch emptiness. |
| Center restrictions | `LcmSix.center_constraints` | Odd X,Y, X>=7 and Y-X>=12 follow from the original domain. |
| An infinite subfamily | `LcmSix.no_collision_of_carry_le` | All n<m with carry(m)<=carry(n); excludes those pairs only. |
| Known gcd obstruction | `LcmSixGcd.common_divisor_square_dvd` | All integer coefficients and common divisors under the exact curve equation. |
| Carry-specialized gcd bounds | Eight `centerGcd_dvd_*` and `slopeGcd_dvd_*` theorems in `CarryGcd.lean` | Necessary conditions for the four exact branches; no upper bound on n,m. |
| Congruence-sieve limitation | Four `ratio_*_survives_every_modulus` theorems in `ModularObstruction.lean` | For every positive modulus, nonnegative disjoint representatives satisfy the product congruence and carry residues. Not integer product equalities or LCM collisions. |

The Lean proof of `defect_six` first proves a universal gcd-periodicity identity, then exhausts its 60 residue classes. This is a finite proof of an explicitly proved periodic formula, not a bounded search over interval starts. The small gcd case splits likewise follow proved uniform bounds on the gcd. Integer subtraction is used in Phi and the centered formulas, so natural subtraction cannot silently truncate a curve coefficient.

`Audit.lean` names 25 declarations. `scripts/check_axioms.py` runs Lean, requires exactly those reports, and rejects every dependency outside `propext`, `Classical.choice`, and `Quot.sound`. All 25 passed; no `sorryAx`, custom mathematical axiom, unproved key assumption, `Lean.ofReduceBool`, or CAS certificate appears in their dependency reports.

## Toolchain and recorded checks

- Lean 4.33.1, compiler commit `819816b2e0a3bf405af45ae5c7af2491d8f5bee6`.
- Mathlib commit `0df444a360eaa60ab8c11dca51a86af692955474`; every transitive revision is in `lake-manifest.json`.
- Local host: macOS arm64. Python exact-arithmetic checker: 3.14.6. Symbolic map checker: SymPy 1.14.0 / mpmath 1.3.0 in a separately created environment.
- Verification date: 2026-10-24 (Asia/Shanghai).

The following commands actually completed with exit 0 in the working checkout:

```sh
lake --wfail build
python3 scripts/check_axioms.py
lake env leanchecker -v LcmSix
python3 scripts/verify_reduction.py
```

The corresponding project logs are in `verification/`. The build completed 1093 jobs; already-built mathlib dependencies were reused. `leanchecker` replayed Core, Reduction, GcdBound, CarryGcd, ModularObstruction and the root module. It rechecks project declarations with Lean's kernel in their imported environments; it is **not an independent implementation of Lean** and does not rebuild the entire mathlib source tree.

The Python script recomputed the product/LCM identity for n=0..9999, all 400 carry residue pairs, and modular constructions at 276 specified moduli. These checks are finite sanity checks, logically separate from the universal Lean proofs. No search absence is used as a proof of noncollision.

The [CAS record](../cas/CAS.md) distinguishes exact symbolic checks, Magma rank/full-basis flags, and missing completeness proofs. Its fresh Python environment reproduced all saved map outputs byte-for-byte. Magma 2.30-1 was used on the official calculator; its saved outputs are exploratory CAS evidence outside Lean.

## Clean-checkout procedure

A clean-checkout replay record will be added after execution. The procedure uses a new git clone with no project object files, while allowing the exact pinned third-party dependencies and their public mathlib cache to be reused. No claim of a from-source rebuild of the entire dependency graph is made.

## Trust and review boundaries

The final definitions, quantifiers, carry hypotheses and domain boundaries were inspected separately from tactic success. Additional agents reconstructed the human mathematics and reviewed the formal endpoint types; this is AI-assisted cross-checking, not an independent human referee report. No external mathematical review or award acceptance is claimed.

Neither successful compilation, source-token scanning, nor finite tests alone establish that a theorem answers the original question. The declarations above deliberately state their narrower scope. The unresolved proof obligation remains emptiness of all four exact branches in the original disjoint domain, or one exact admissible collision.
