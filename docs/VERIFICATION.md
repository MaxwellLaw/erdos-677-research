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
| Height certificate algebra | `HeightCertificates.common_divisor_of_bezout7` and five declarations in each of four branch namespaces in `HeightCertificates.lean` | Integer Bézout identities, common-divisor bounds, and exact coefficient sums C,D. No canonical-height or real-logarithm theorem is asserted by these Lean declarations. |
| Congruence-sieve limitation | Four `ratio_*_survives_every_modulus` theorems in `ModularObstruction.lean` | For every positive modulus, nonnegative disjoint representatives satisfy the product congruence and carry residues. Not integer product equalities or LCM collisions. |

The Lean proof of `defect_six` first proves a universal gcd-periodicity identity, then exhausts its 60 residue classes. This is a finite proof of an explicitly proved periodic formula, not a bounded search over interval starts. The small gcd case splits likewise follow proved uniform bounds on the gcd. Integer subtraction is used in Phi and the centered formulas, so natural subtraction cannot silently truncate a curve coefficient.

`Audit.lean` now names 46 declarations, including 21 added for the height-certificate algebra. `scripts/check_axioms.py` runs Lean, requires exactly those reports, and rejects every dependency outside `propext`, `Classical.choice`, and `Quot.sound`. All 46 passed; no `sorryAx`, custom mathematical axiom, unproved key assumption, `Lean.ofReduceBool`, or CAS certificate appears in their dependency reports.

## Toolchain and recorded checks

- Lean 4.33.1, compiler commit `819816b2e0a3bf405af45ae5c7af2491d8f5bee6`.
- Mathlib commit `0df444a360eaa60ab8c11dca51a86af692955474`; every transitive revision is in `lake-manifest.json`.
- Local host: macOS arm64. Python exact-arithmetic checker: 3.14.6. Symbolic map checker: SymPy 1.14.0 / mpmath 1.3.0 in a separately created environment.
- Verification date: 2026-10-24 (Asia/Shanghai).

At the initial publication checkpoint, the following commands actually completed with exit 0 in the working checkout:

```sh
lake --wfail build
python3 scripts/check_axioms.py
lake env leanchecker -v LcmSix
python3 scripts/verify_reduction.py
```

The corresponding initial project logs are in `verification/`. The build completed 1093 jobs; already-built mathlib dependencies were reused. `leanchecker` replayed Core, Reduction, GcdBound, CarryGcd, ModularObstruction and the root module. It rechecks project declarations with Lean's kernel in their imported environments; it is **not an independent implementation of Lean** and does not rebuild the entire mathlib source tree.

The Python script recomputed the product/LCM identity for n=0..9999, all 400 carry residue pairs, and modular constructions at 276 specified moduli. These checks are finite sanity checks, logically separate from the universal Lean proofs. No search absence is used as a proof of noncollision.

The [CAS record](../cas/CAS.md) distinguishes exact symbolic checks, Magma rank/full-basis flags, and missing completeness proofs. Its fresh Python environment reproduced all saved map outputs byte-for-byte. Magma 2.30-1 was used on the official calculator; its saved outputs are exploratory CAS evidence outside Lean.

## Clean-checkout procedure

A new git clone of commit `0d171ab2284e3dc55595d529116405438642a6b3`, with no project object files, completed all four commands above with exit 0; the symbolic map checker also passed with byte-identical output. Its tracked working tree remained clean. All six project modules were rebuilt. The exact pinned third-party dependency directory was linked from the original checkout, reusing downloaded public mathlib cache objects; the separate pinned SymPy environment was also reused for this replay. Logs are `verification/clean-build.log`, `clean-axioms.log`, `clean-leanchecker.log`, and `clean-python.json`. No from-source rebuild of the entire dependency graph is claimed. Subsequent initial-publication changes through `cee4d331d4b65394a6282b9521e8212db602daa5` contain only documentation, attribution and validation records. `verification/source-hashes.json` preserves those initial tested hashes; it is not the manifest for the later height-certificate addition.

## Height-certificate verification, 2026-10-24

The new integer algebra is in `LcmSix/HeightCertificates.lean`. Its eight Bézout identities hold for all integer p,q. Its four common-divisor endpoints assume `IsCoprime p q` and divisibility of the two explicitly defined quartics; they conclude divisibility of the displayed positive integer R. The generic proof also includes zero and negative coordinate/divisor cases permitted by its hypotheses. The eight C,D theorems evaluate the exact absolute coefficient sums. An independent coefficient-by-coefficient comparison found these models, witnesses, R,C,D equal to the saved JSON inputs.

The following commands completed with exit 0 in the working checkout:

```sh
lake --wfail build
python3 scripts/check_axioms.py
lake env leanchecker -v LcmSix
python3 scripts/verify_reduction.py
python3 scripts/verify_heights.py
```

The build reported 1096 jobs, reusing dependency objects. The axiom audit passed all 46 named declarations. `leanchecker` replayed all seven project modules, including HeightCertificates. Actual outputs are `verification/height-build.log`, `height-axioms.log`, `height-leanchecker.log`, `height-reduction.json`, and `height-python.log`. The tested code, exact inputs and mathematical outputs are pinned by `verification/height-source-hashes.json`.

The separate standard-library Python verifier recomputes the polynomial identities, seven rational doublings for each of 24 point inputs, outward rational logarithm intervals, and positive principal minors of four rational matrices. It proves the numerical certificate obligations used in the [human height proof](../cas/height-bounds/README.md): globally `H(P)-h(x(P))<5`, and `H(sum m_i P_i)>=sum m_i^2/100` on each displayed generated subgroup. Every mathematical JSON field must match the saved output; only the Python runtime string is excluded. The saved output has SHA256 `2a988af3758fc58d84e7220160fc608e73194f703033099c96a97b580595f450`. A separate replay reproduced it byte-for-byte on Python 3.14.6.

This numerical certification is exact arithmetic plus the stated human canonical-height argument. Its logarithm bounds, limiting argument, quadraticity and matrix analysis are **not Lean theorems**. Only the specified integer algebra is kernel checked. Extending the subgroup statement to a representation of every rational point still uses the separately recorded Magma full-basis assertion; this calculation does not independently certify saturation. No finite coefficient search, effective initial coefficient bound, elliptic-logarithm lower bound or LLL completeness conclusion is supplied.

### Clean clone of the height-certificate checkpoint

A fresh clone of `d1943b5e9ca475f0922101786d2ae56387c96973`, initially without project object files, completed all five commands above with exit 0. All seven project modules were rebuilt, all 46 axiom reports passed, kernel replay succeeded, and both Python checks passed. Its tracked working tree remained clean. Only the pinned `.lake/packages` directory was linked from the working checkout; downloaded public dependency cache objects were reused. This replay did not require SymPy, a network CAS, or a full source rebuild of Mathlib.

The machine-readable command/exit record is `verification/height-clean-record.json`; full logs are `height-clean-build.log`, `height-clean-axioms.log`, `height-clean-leanchecker.log`, `height-clean-reduction.log`, and `height-clean-python.log` in the same directory. Subsequent changes in this checkpoint add those validation records and clarify documentation only; the tested source/certificate hashes remain those in `verification/height-source-hashes.json`.

## Trust and review boundaries

The final definitions, quantifiers, carry hypotheses and domain boundaries were inspected separately from tactic success. Additional agents reconstructed the human mathematics and reviewed the formal endpoint types; this is AI-assisted cross-checking, not an independent human referee report. No external mathematical review or award acceptance is claimed.

Neither successful compilation, source-token scanning, nor finite tests alone establish that a theorem answers the original question. The declarations above deliberately state their narrower scope. The unresolved proof obligation remains emptiness of all four exact branches in the original disjoint domain, or one exact admissible collision.
