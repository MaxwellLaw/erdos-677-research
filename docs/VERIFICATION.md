# Statement correspondence and actual verification

This document verifies the auxiliary results in this repository. **There is no Lean theorem proving all k=6 starts collision-free, and no theorem resolving all lengths. The later analytic/computational result and its separate trust boundary are described below.**

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
| Integer lattice distances | Four generic theorems and 25 validity/distance pairs in `LatticeDistance.lean` and `LatticeCertificates.lean` | Every integer coefficient quadruple; explicit original rounded inputs and strict radius. No real-logarithm, rank, or k=6 endpoint assumption. |
| Real rounding transfer | `rounding_error_bound`, `Certificate.real_linear_form_large` | Explicit rounding-error and coefficient hypotheses imply a strict bound on the scaled real linear form. Actual elliptic-logarithm enclosures remain external. |
| Abstract saturation bridge | Three theorems in `SaturationBridge.lean` | Joint reduction detection and no ell-torsion imply ell-saturation; no claim that an actual elliptic curve satisfies these hypotheses. |
| Real duplication bounds | `DuplicationBounds.Branch*.global_lower`, `integer_lower` | Every real or integer p,q on each of the four actual quartic pairs, with all 34 Bernstein leaves and two-chart coverage proved. |
| Logarithmic transfer | `DuplicationBounds.logarithmic_defect`, `Branch*.defect_bounds` | Explicit divisor bounds and nonzero coordinate pair; specialized strong gcd bounds remain hypotheses here. |
| Elementary canonical limit | `CanonicalLimit.tendsto_normalized`, `limit_tail_bounds`, `canonical_map`, `limit_eq_of_bounded_difference`, `canonical_unique` | Explicit bounded recurrence defects; convergence, asymmetric tails, scaling, bounded-change invariance and uniqueness are proved. |
| Actual coordinate dynamics | `PrimitiveDynamics.branch*_converges`, `branch*_height_error`; `Model.canonical_enclosure` | All primitive integer pairs; actual gcd-normalized steps, with every polynomial/divisor premise discharged for all four models. Proves H-h<5; actual elliptic-group identification is now covered by the next row, and actual pairing is covered by the later pairing row. |
| Actual elliptic doubling and heights | 33 declarations in `EllipticDuplication.lean` | Every point of the four exact rational curves; group doubling, primitive representatives, projective naive-height equality, canonical-limit convergence, scaling, finite-iterate bounds and H-h<5, including infinity and y=0. Four nonzero discriminants and IsElliptic instances are proved. |
| Conditional canonical quadraticity | 18 declarations in `CanonicalQuadratic.lean` | An arbitrary abelian group with an explicit uniform bounded naive parallelogram defect; convergence, exact parallelogram, symmetric biadditive pairing and all integer homogeneity follow. The separate actual pairing module now discharges the defect premise on the four curves. |
| Actual addition/subtraction compatibility | Eight declarations in `EllipticAddSub.lean` | Rational a1=a3=0 models; the actual Mathlib group operations and map agree projectively with a nonzero scalar for every point pair, including all exceptional charts. Prior general Mathlib main work is credited. |
| Actual canonical pairing | 22 declarations in `EllipticParallelogram.lean` | Bounded naive parallelogram error, exact canonical law, symmetric biadditive pairing, all integer homogeneity, nonnegativity and finite Gram expansion. Four concrete branch endpoints discharge model and defect premises. Numerical Gram bounds are discharged by the subsequent rows. |
| Actual point and orbit certificates | 135 declarations in `HeightPoints.lean` and `HeightOrbits.lean` | 24 actual points, 12 actual sums, 168 finite projective steps, final Bezout primitivity, and exact naive heights of all actual seventh doubles. Ordinary kernel arithmetic; no external orbit premise. |
| Real logarithm certificates | Six `LogBounds` theorems and 32 `LogCertificates` endpoints | Analytic inequalities from Mathlib plus kernel-checked rational series and natural-number binary brackets prove every required real log enclosure. |
| Actual canonical-height intervals | `HeightEnclosure.from_seven_steps` and 24 `HeightIntervals` endpoints | Every actual finite orbit, log and rounding premise is discharged; the original closed intervals hold for the actual group heights. |
| Numerical Gram lower bounds | 27 declarations in `GramBounds`/`GramCertificates`, six in `HeightGram` | Rational square factorizations, interval-error bounds and actual group expansion; intermediate six-height premises are explicit. |
| Unconditional actual subgroup endpoints | Ten declarations in `HeightLowerBound.lean` | Four numerical lower bounds for all integer triples and four relation-triviality consequences, with actual points and no remaining numerical premise. Also H(0)=0 and the generic coefficient argument. Full-group generation and the complete k=6 endpoint remain separate. |
| Congruence-sieve limitation | Four `ratio_*_survives_every_modulus` theorems in `ModularObstruction.lean` | For every positive modulus, nonnegative disjoint representatives satisfy the product congruence and carry residues. Not integer product equalities or LCM collisions. |

The Lean proof of `defect_six` first proves a universal gcd-periodicity identity, then exhausts its 60 residue classes. This is a finite proof of an explicitly proved periodic formula, not a bounded search over interval starts. The small gcd case splits likewise follow proved uniform bounds on the gcd. Integer subtraction is used in Phi and the centered formulas, so natural subtraction cannot silently truncate a curve coefficient.

`Audit.lean` now names 494 declarations: the previous 253 plus 241 for actual points, finite orbits, real logarithms, height intervals, rational matrices and unconditional subgroup endpoints. Earlier dated checkpoints below retain their historical counts. `scripts/check_axioms.py` runs Lean, requires exactly those reports, and rejects every dependency outside `propext`, `Classical.choice`, and `Quot.sound`. The parser also recognizes Lean's explicit "does not depend on any axioms" output for the new arithmetic declarations; the allowed dependency set is unchanged; no `sorryAx`, custom mathematical axiom, unproved key assumption, `Lean.ofReduceBool`, or CAS certificate appears in their dependency reports.

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

At this original numerical checkpoint the certification was exact arithmetic plus the stated human canonical-height argument; only the specified integer algebra was kernel checked. The subsequent 27 October numerical Gram layer now proves the actual subgroup endpoint in Lean. Full-group generation is established by the separate independent written rank/saturation proof, which replaced the earlier Magma completion flags; it is still not a complete Lean group-generation theorem. That height-only checkpoint supplied no initial coefficient bound or lattice completeness conclusion; the subsequent global calculation is recorded below.

### Clean clone of the height-certificate checkpoint

A fresh clone of `d1943b5e9ca475f0922101786d2ae56387c96973`, initially without project object files, completed all five commands above with exit 0. All seven project modules were rebuilt, all 46 axiom reports passed, kernel replay succeeded, and both Python checks passed. Its tracked working tree remained clean. Only the pinned `.lake/packages` directory was linked from the working checkout; downloaded public dependency cache objects were reused. This replay did not require SymPy, a network CAS, or a full source rebuild of Mathlib.

The machine-readable command/exit record is `verification/height-clean-record.json`; full logs are `height-clean-build.log`, `height-clean-axioms.log`, `height-clean-leanchecker.log`, `height-clean-reduction.log`, and `height-clean-python.log` in the same directory. Subsequent changes in this checkpoint add those validation records and clarify documentation only; the tested source/certificate hashes remain those in `verification/height-source-hashes.json`.

## Global analytic and residual verification, 2026-10-24 evening

The [scoped theorem](../cas/global-bound/README.md) excludes every original-domain square point whose image lies in the specified rank-three subgroup, in each of four models. David's theorem gives `M<10^100`; 25 exact lattice-distance steps give the closed bounds `[60,60,62,64]`. Two independently implemented finite-field sieves then exhaust the same 7,642,936 coefficient triples and reconstruct the same 46 residual rational points. None satisfies the original disjointness and square conditions. The three odd-square inverses with U,V>=49 give only overlapping intervals `(13,15)`, `(5,6)`, `(3,4)`.

The primary sieve uses complete cyclic-group tables at 30 good primes per curve. The second uses complete-group translation permutations at 30 different good primes above 257, including noncyclic groups. Their candidate ordering, group representation and rational reconstruction implementations differ. Both retain every identity/zero-denominator reduction conservatively. The replay compares every residual coefficient triple, rational point, inverse pair and classification; it also checks that the prime sets are disjoint. This is independent arithmetic implementation, not an external human referee report.

The working checkout completed `python3 scripts/verify_global_bound.py` with exit 0; the actual output is `verification/global-replay.log`. It reruns the prior height certificate, algebraic height parameters, period-area bounds, David scalar constants, rigorous real-log intervals, the independent lattice checker, and both exhaustive sieves. Saved mathematical outputs must match exactly; only top-level Python runtime metadata is omitted from comparisons. No floating-point estimate is used as a proof bound. The proposal generator's first attempt with SymPy LLL raised an internal assertion; it was replaced by explicit rational basis reduction. The independent checker verifies unimodularity and distances directly and assumes no LLL quality assertion.

The official Magma service was rerun with the unchanged `cas/mordell_weil.m`, seed 550. Magma 2.30-1 again returned the same four bases, free groups Z^3, and `rankproved=true`, `fullproved=true`; the complete mathematical stdout matches the initial saved record. The new raw transcript is `cas/global-bound/mordell_weil_recheck.result.json`. No GRH setting or analytic-rank assumption was enabled. Those flags remain external CAS certification, not independently exported descent/saturation certificates. Together with the subgroup result they give a CAS-supported computational k=6 corollary. They do not supply a Lean k=6 theorem or settle all lengths.

All 46 existing Lean audit declarations are unchanged. The new analytic arguments, elliptic-integral identities, finite-group reduction theorem and Python arithmetic are outside the Lean kernel. They are documented rather than imported as axioms. Primary sources and their normalization conventions are fixed in the new proof notes. `verification/global-source-hashes.json` records the code and mathematical artifact set for this checkpoint.

### Clean clone of the global computation checkpoint

A fresh clone of `42ea95b0cad686a5ca1d3575e6e9bba4d1a74756`, with no project objects initially present, completed all of the following with exit 0:

```sh
lake --wfail build
python3 scripts/check_axioms.py
lake env leanchecker -v LcmSix
python3 scripts/verify_reduction.py
python3 scripts/verify_global_bound.py
# Using the separate environment pinned by cas/requirements-cas.txt:
python cas/verify_k6_maps.py
```

All seven Lean modules rebuilt, all 46 axiom reports used only the standard logical axioms, and project kernel replay passed. The global replay executed every arithmetic stage and both exhaustive implementations; the symbolic-map output was byte-identical to the saved original. The clone remained clean. Only pinned third-party dependency/cache directories and the separately pinned SymPy environment were reused. No network CAS was used in this clean replay; the Magma recheck described above was a separate recorded run.

Actual commands and exit codes are in `verification/global-clean-record.json`; full output is in `global-clean-build.log`, `global-clean-axioms.log`, `global-clean-leanchecker.log`, `global-clean-reduction.log`, `global-clean-global.log`, and `global-clean-maps.log` in that directory. The subsequent publication changes add these records and correct two explanatory documentation sentences; no tested code or certificate changed.

## Independent group and lattice formalization checkpoint, 2026-10-25

The new lattice modules prove the integral dual-functional distance argument,
all 25 concrete integer certificates, and conditional transfer to real linear
forms with explicit rounding/coefficient hypotheses. `SaturationBridge.lean`
proves three abstract reduction criteria; it does not instantiate them with
elliptic curves. The working build completed 1283 jobs, all 105 explicit axiom
reports passed with only standard logical axioms, and Lean kernel replay
covered all eleven project modules. The 59 added audited declarations do not
include a complete k=6 endpoint.

The independent mathematical group proof has two parts. `cas/saturation/`
proves torsion-freeness, H(P)>1/10 globally, regulator<8/5, index in the saturated
hull below 80, and complete saturation using the 26 primes up to 101. Its
small-height search is exhaustive under the proved global bound: the four
boxes have B=19,86,234,113 and contain 51 points modulo y-sign, all excluded
from low height by exact two-doubling inequalities. `cas/descent/` independently
certifies maximal orders, class-group dimension upper bounds by a complete
Minkowski ideal set, Kummer support, and the final local-3 rank restriction.
It proves rank three and hence complete rational-point generation. No Magma
class-group, Selmer-dimension, rank or full-basis flag is assumed.

The finite-field verifier uses a different counting/addition method from its
witness producer. The small-height verifier checks Bernstein identities by
expansion, uses rational group addition for doubling, and checks regulator
corners. The ideal audit independently checks all 2470 HNF operations through
lattice containment and 158676 maximal minors, and all 438 characteristic
polynomials by separate formulas. The local-3 verifier uses Sylvester resultants
and characteristic-polynomial integrality, different from discovery. Each
mathematical interpretation remains the explicit human proof; agreement of
programs is not a substitute for that argument.

### Clean clone of the independent group checkpoint

A new clone of `5a7eb71fc99513c133d5300059074498b4cbd0bc`, initially without
project object files, completed all nine commands from the
[k=6 reproduction entry](K6_THEOREM.md) with exit 0: project build, 105-declaration
axiom audit, eleven-module kernel replay, original reduction sanity check,
25-certificate correspondence, complete global-bound/residual replay, complete
saturation replay, complete independent descent replay, and symbolic maps.
The map output was byte-identical to the saved certificate and the tracked
working tree remained clean.

The clone linked only the pinned third-party `.lake/packages` directory and
reused the separate pinned SymPy environment. All eleven project modules
were rebuilt. No Magma service was invoked, and no from-source rebuild of
all Mathlib dependencies is claimed. Full output is in
`verification/independent-clean-*.log`; exact command/exit records and path
normalization are in `verification/independent-clean-record.json`. Subsequent
publication changes add these records and update cross-references in prose;
no tested Lean/Python source or mathematical certificate changed.

## Trust and review boundaries

The final definitions, quantifiers, carry hypotheses and domain boundaries were inspected separately from tactic success. Additional agents reconstructed the human mathematics and reviewed the formal endpoint types; this is AI-assisted cross-checking, not an independent human referee report. No external mathematical review or award acceptance is claimed.

Neither successful compilation, source-token scanning, nor finite tests alone establish that a theorem answers the original question. The declarations above deliberately state their narrower scope. The later calculation excludes those branches in four explicit generated subgroups. The subsequent independent rank and saturation proof extends that exclusion to all rational points without Magma completion flags. Its mathematical theory and exact Python arithmetic remain outside Lean; a complete Lean k=6 endpoint is unfinished. The unrestricted all-length question remains unresolved.

## Real-bound and coordinate-height formalization, 2026-10-25 evening

Six added Lean modules prove the [precise coordinate-dynamics statements](../cas/height-bounds/LEAN_DYNAMICS.md).
The concrete convergence and strict H-h<5 endpoints have only a primitive
integer pair as input. They have no assumed height defect, convergence,
external numerical certificate or unspecified model proof. The total step
uses the actual positive gcd; integer divisibility proves that division is
exact and the output remains primitive. The finite-iterate enclosures use
the coarse existing integral Bezout R, not the stronger rational-point-only
gcd bound from the independent saturation argument.

The elementary limit proofs formalize standard height-limit theory; this is
a new formalization contribution, not a claim to new canonical-height theory.
The 34 rational Bernstein witnesses are the previously published exact data;
new proofs verify their full real-domain implications inside Lean. The
exporter checks their exact correspondence with the saved input. Elliptic
group-law identification, quadraticity and the remaining k=6 chain are still
outside these new endpoints. The [uniform two-factor note](UNIFORM_STRUCTURE.md)
is a separate written necessary condition and is not part of the Lean audit.

The working checkout completed `lake --wfail build` (1988 jobs),
`python3 scripts/check_axioms.py` (172 explicit declarations),
`lake env leanchecker -v LcmSix` (all seventeen project modules), and
`python3 scripts/export_duplication_certificates.py`, all with exit 0.
Actual output is in `verification/dynamics-build.log`, `dynamics-axioms.log`,
`dynamics-leanchecker.log`, and `dynamics-correspondence.log`. The pinned
public dependency cache was reused. No new collision enumeration was needed
for these additions; the existing complete residual proof and certificates
are unchanged. The fresh-clone replay is recorded next.

### Fresh clone of the coordinate-dynamics checkpoint

A new clone of `972f1d2c084ddfca72b2d2a7c904dd85be42b699`, with no project
objects initially present, passed all seven commands below with exit 0:

```sh
lake --wfail build
python3 scripts/check_axioms.py
lake env leanchecker -v LcmSix
python3 scripts/export_duplication_certificates.py
python3 scripts/export_lattice_certificates.py
python3 scripts/verify_heights.py
python3 cas/saturation/verify_all.py
```

All seventeen project modules rebuilt and replayed; all 172 explicit axiom
reports used only the standard logical axioms. The clone's tracked tree
remained clean. Only the pinned third-party `.lake/packages` directory was
linked from the working checkout, reusing its public dependency cache. No
network CAS, SymPy environment or from-source Mathlib rebuild was used.
The unchanged global residual enumeration and descent certificates were not
rerun as a new research experiment for this formalization change; their
previous complete replay remains recorded above and the existing CI checks
continue to cover them.

Exact commands, exit codes and durations are in
`verification/dynamics-clean-record.json`; output is in
`verification/dynamics-clean-{build,axioms,kernel,duplication,lattice,heights,saturation}.log`.
The only subsequent changes in this publication add this record and logs;
no tested Lean/Python source or mathematical certificate changed.

The subsequent component-resonance and pure-cycle exclusion note changes only
written research documentation. Its symbolic proof and explicit inequalities
were separately reconstructed; no claim is made that it is a Lean theorem
or a numerically enumerated result. The tested Lean/Python source and original
exact certificates are unchanged from the clean source SHA above.

## Actual elliptic-group and quadraticity checkpoint, 2026-10-26

The two new modules add 51 explicit audited declarations, bringing the total
to 223. `EllipticDuplication.lean` proves the actual group-doubling connection,
naive-height identity and four unconditional group convergence/H-h<5 pairs.
`CanonicalQuadratic.lean` proves the standard limit/polarization theorem
under its explicit bounded naive parallelogram premise. At this morning checkpoint that premise had
not been proved for the four actual curves; the evening checkpoint below discharges it. See the
[exact definitions and remaining boundary](LEAN_ELLIPTIC_HEIGHT.md).

The final working build completed 3411 jobs with exit 0, the 223-declaration
axiom audit passed, and `leanchecker` replayed all nineteen project modules.
The five cubic obstruction witnesses passed both a complete finite-field
root test and an independent Euler-discriminant test; these do not enumerate
LCM collisions. The first check also requires exact agreement with its saved
JSON certificate. Source/hypothesis review independently covered all
exceptional point charts and the low-degree mathematical proof. It is not
an external referee report.

Commands were `lake --wfail build`, `python3 scripts/check_axioms.py`,
`lake env leanchecker -v LcmSix`,
`python3 cas/uniform/cubic_obstruction_certificate.py` and
`python3 cas/uniform/verify_cubic_discriminants.py`. Actual logs are
`verification/elliptic-{build,axioms,kernel,cubic,cubic-independent}.log`.
Pinned public Mathlib dependency objects were reused. No network CAS or
SymPy was required by these proof and witness replays. The unchanged earlier
global enumeration is not presented as new research or rerun to create new
evidence of noncollision.

### Clean clone of the actual elliptic-group checkpoint

A fresh clone of `524fd021ab744a14a8a02bd243ef6145d802f1e3`, initially without
project object files, completed all five commands above with exit 0. All
nineteen project modules rebuilt and kernel replayed; all 223 explicit
axiom reports passed. Both cubic witness implementations passed, and every
file in `verification/elliptic-source-hashes.json` matched. The tracked
clone remained clean. The recorded Python runtime was 3.14.6.

Only the pinned third-party `.lake/packages` directory was linked. No
network CAS or SymPy environment was used, and no full from-source Mathlib
rebuild is claimed. Machine-readable commands/exits are in
`verification/elliptic-clean-record.json`; full logs are
`elliptic-clean-{build,axioms,kernel,cubic,cubic-independent}.log` in the
same directory. Subsequent publication changes add this record and the
written quantitative branching consequence only; tested Lean/Python source,
workflow and certificates remain unchanged.

## Actual canonical pairing and local branching, 2026-10-26 evening

`EllipticAddSub.lean` adds eight audited theorems covering the actual
addition/subtraction map, including all exceptional point charts.
`EllipticParallelogram.lean` adds 22 audited declarations: actual bounded
naive parallelogram error, canonical parallelogram law, symmetric biadditive
pairing, integer quadraticity and a finite Gram expansion. The four concrete
curves discharge the ellipticity assumptions. The project now audits 253
declarations across 21 project modules. The actual-curve bounded-defect
premise is no longer an open formalization obligation.

The working `lake --wfail build` completed 3416 jobs;
`python3 scripts/check_axioms.py` and
`lake env leanchecker -v LcmSix` also returned exit 0. The axiom reports
contain only Lean's standard logical axioms. Exact commands, durations and
exits are in `verification/pairing-working-record.json`; output is in
`verification/pairing-{build,axioms,kernel}.log`. An independent copied-source
replay of both new files also passed `lean --trust=0` and `leanchecker`,
without importing the two target object files; it reused dependency objects.
The new symbolic [local branching argument](UNIFORM_LOCAL_BRANCHING.md) was
independently reconstructed. It has not been Lean-formalized and performs
no new collision enumeration.

[Prior work](LEAN_PAIRING.md#prior-formalization-and-the-scope-of-this-integration)
credits Michael Stoll's earlier, more general Mathlib main results with
full source commits. This is a fixed-version integration and concrete
canonical-height application, not a claim to first formalization.
The numerical Gram bounds and the remaining k=6 certificate chain still
need a Lean connection. The complete Lean k=6 endpoint and arbitrary-k
original problem remain unfinished.

### Clean clone of the actual canonical-pairing checkpoint

A fresh clone of `85e0151679b57ebbe7802f549de5552ac2348864`, initially
without project object files, passed all three commands above with exit 0.
The build completed 3416 jobs, all 21 project modules were rebuilt and kernel
replayed, and all 253 explicit axiom reports passed. The 29 source/workflow/
dependency files in `verification/pairing-source-hashes.json` matched. The
tracked clone remained clean. Python was 3.14.6.

Only the pinned third-party `.lake/packages` directory was linked; no project
object files were copied. No network CAS, SymPy environment or full
from-source Mathlib rebuild was used. Commands, exits and durations are in
`verification/pairing-clean-record.json`; outputs are in
`verification/pairing-clean-{build,axioms,kernel}.log`. The unchanged global
certificate chain is still covered by the existing CI. It was not rerun as
a new research enumeration for these symbolic and Lean changes.

Subsequent publication changes add these verification records and correct
a documentary comparison of lower-height constants: all four models have
`32*R<D`, so the formal lower tail is stronger than the original Gram
script's tail. This is distinct from the stronger rational-point local gcd
bound still needed for the separate small-height argument. No tested Lean/
Python source, workflow or mathematical certificate changed after the clean
source commit.

## Actual numerical subgroup bounds, 2026-10-27 morning

Ten new modules add 241 explicit audited declarations. All 24 actual points,
12 sums, 24 seven-step orbits, 32 logarithm enclosures, 24 original height
intervals and four exact matrix factorizations connect to four unconditional
actual subgroup bounds and four integer-independence consequences. See
[the complete scoped statement](NUMERICAL_GRAM.md).

Independent source/arithmetic review directly parsed the Lean certificate
fields and checked all 168 F/G steps, nonzero scalars, final Bezout witnesses,
original saved coordinates, 60 unit-series enclosures, 32 binary/log
certificates and all four rational matrix factorizations. It also reviewed
the actual group types and every remaining hypothesis. This is an internal
independent implementation audit, not an external referee report. The Lean
proofs do not rely on the Python audit or exporter succeeding.

The `decide` uses are ordinary kernel reductions. The exponentiation threshold
is raised to 300000 to evaluate the largest recorded exponent 221661, without
native evaluation or additional axioms. The axiom parser was updated to
recognize Lean's zero-axiom report format while preserving the same allowed
standard logical axioms and exact required-name set.

The final working project build completed 3614 jobs. The 494-declaration
axiom audit passed, and `leanchecker` replayed all 31 project modules with
exit 0. All four new exporter correspondence checks also passed. Exact
commands, exits and durations are in
`verification/numerical-working-record.json`; output is in
`verification/numerical-{build,axioms,kernel,orbits,logs,intervals,gram}.log`.
The pinned third-party cache was reused. No CAS service, SymPy, floating-point
logarithm or new collision search was used for this addition.

`verification/numerical-independent-audit.json` records the independent
source/arithmetic review and its frozen source hashes. The full selected
source/workflow/dependency manifest is
`verification/numerical-source-hashes.json` (47 files). The existing global
residual, descent and saturation certificates are unchanged; CI continues
to replay them as existing verification, not as new research enumeration.

### Fresh clone of the actual numerical-height checkpoint

A fresh clone of `3baf2947683b4943b45927d44b1d8bf7a94a3c19`, initially
without project object files, completed all seven commands above with exit 0.
The build completed 3614 jobs and rebuilt all 31 project modules. All 494
explicit axiom reports passed, and all 31 modules were kernel replayed.
All four new exporter checks passed and all 47 manifest files matched.
The tracked clone remained clean; its Python runtime was 3.14.6.

Only the pinned third-party `.lake/packages` directory was linked. No project
objects were copied, no full from-source Mathlib rebuild is claimed, and no
network CAS or SymPy was used. Exact commands, exits and durations are in
`verification/numerical-clean-record.json`; logs are
`verification/numerical-clean-{build,axioms,kernel,orbits,logs,intervals,gram}.log`.

Subsequent publication changes add these records and clarify that the remaining
height obligation is the stronger global minimum-height/index argument. All
tested Lean/Python source, workflows and mathematical certificates are unchanged
from the clean source SHA.
