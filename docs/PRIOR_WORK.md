# JSP-000550 prior-work and submission audit

Audit date: 2026-10-23 (Asia/Shanghai). This is a source and scope audit, not a new execution of any third-party Lean project.

## Applicable awards revision and rules

The main branch of TheJustinSunPrize/awards was directly resolved through the GitHub commits API to **5b7126acf3d3d31c71e5964525807d1532cba892**, committed 2026-10-22T08:15:22Z. All rules below were read at that revision:
- [CONTRIBUTING.md](https://github.com/TheJustinSunPrize/awards/blob/5b7126acf3d3d31c71e5964525807d1532cba892/CONTRIBUTING.md)
- [PR template](https://github.com/TheJustinSunPrize/awards/blob/5b7126acf3d3d31c71e5964525807d1532cba892/.github/PULL_REQUEST_TEMPLATE.md)
- [Award process](https://github.com/TheJustinSunPrize/awards/blob/5b7126acf3d3d31c71e5964525807d1532cba892/docs/award-process.md)
- [Claim form](https://github.com/TheJustinSunPrize/awards/blob/5b7126acf3d3d31c71e5964525807d1532cba892/.github/ISSUE_TEMPLATE/claim-award.yml)
- [MathDB pilot register](https://github.com/TheJustinSunPrize/awards/blob/5b7126acf3d3d31c71e5964525807d1532cba892/problems/mathdb-pilot.md)
- [Verification guide](https://github.com/TheJustinSunPrize/awards/blob/5b7126acf3d3d31c71e5964525807d1532cba892/docs/verification.md)
- [Attribution rules](https://github.com/TheJustinSunPrize/awards/blob/5b7126acf3d3d31c71e5964525807d1532cba892/docs/attribution.md)

The [catalog entry](https://github.com/TheJustinSunPrize/awards/blob/5b7126acf3d3d31c71e5964525807d1532cba892/problems/catalog-0501-0600.md#JSP-000550) describes disjoint equal-length consecutive positive-integer intervals, with Current status Open, Lean proof No and Eligible to claim No. JSP-000550 is absent from the 50-problem MathDB pilot register, so the legacy process applies at this revision.

Only complete solutions of the original problem qualify for mathematical or Lean submission. Fixed-length results, intermediate lemmas, weaker results and conditional arguments with additional unproved assumptions do not qualify. A valid Lean submission must also identify a complete mathematical solution with supporting evidence. A proof build cannot replace that mathematical review.

For an eligible full solution, the contribution PR changes only the relevant catalog references/text: no Lean source, archives, vendored dependencies or binaries belong in awards. The original public proof repository must be owned by the submitting account or an organization with independently checkable contribution attribution. Supply branch, full 40-character selected SHA, theorem locations, precise original-statement correspondence, dependencies, build commands and actual axiom results. The optional lean-verify workflow is recommended but not mandatory.

Legacy claims require a merged contribution PR, except the narrow recorded-mathematical-solver exception. Lean claims always need a merged contribution PR.

Each role's 14-day review starts only with candidate registration and public notice. A PR, merge, successful build or claim issue does not by itself start that clock or establish an award. Review relevant competing submissions again before an initial submission and before any claim.

## All-state search method and limits

GitHub connector searches were supplemented by direct read-only GitHub REST search and pull-request endpoints. Queries did not restrict open/closed state, so merged and unmerged closed records were included. Search result payloads reported incomplete_results=false for the recorded API queries. Search coverage is evidence of the queries executed, not a guarantee that no work exists under an undiscovered name.

The exact JSP-000550 search in awards returned three PRs and no claim/issue records:
- #4288, open, not merged.
- #4846, open, not merged.
- #3543, closed, not merged.

Other searches combined Erdos677, Erdős 677, erdosproblems.com/677, equal-length intervals, LCM collision, Prime-Power Transport, qrdlgit, erdos677-curve-visualisation, Danesh and Bianchetti. Numeric searches were manually filtered because unrelated PR #677 and JSP-000677 records are not Erdős Problem 677. Awards searches for the paper authors, paper phrase and the two direct proof-repository names returned no matching submission. No award eligibility or global priority conclusion is inferred from search absence.

## The three specified awards PRs

### #4846: two closed arithmetic examples, not a quantified theorem

[PR #4846](https://github.com/TheJustinSunPrize/awards/pull/4846) currently selects qzxuwenlong/jsp-lean-solutions at **c67915b1e14145c696c647a40af4b2fb8faa878a**, file [jsp550.lean](https://github.com/qzxuwenlong/jsp-lean-solutions/blob/c67915b1e14145c696c647a40af4b2fb8faa878a/jsp550.lean#L23). Its theorem jsp550 is one closed conjunction, ending in True, proved by decide. It checks:
- lcm(1,2,3)=6 and lcm(4,5,6)=60, including elementary endpoint inequalities.
- lcm(2,3,4,5)=60 and lcm(6,7,8,9)=504, again with endpoint inequalities.

There are no universally quantified n, m or k in that theorem. It neither proves k=6 nor settles any arbitrary fixed-length case. The selected file imports no custom dependency. No build was rerun for this audit because the theorem type already determines its limited scope.

The PR body's older introduction also names branch jsp-550b and SHA 76abeae68b61b724d94fe3caec938ba0c1e17a49. The actual current catalog diff and structured submission select the later c67915... version above. Those versions must not be conflated.

A [maintainer comment dated 2026-10-22](https://github.com/TheJustinSunPrize/awards/pull/4846#issuecomment-6332538906) rejects partial results and says the PR is being closed. Both connector metadata and direct GitHub search currently still report state=open, merged_at=null. Record the textual rejection and actual API state separately; do not report that closure has happened.

### #4288: wrong Erdős problem

[PR #4288](https://github.com/TheJustinSunPrize/awards/pull/4288) identifies JSP-000550 as Erdős #550 and cites plby/lean-proofs at **8822f7ddef30fadbd92e1c6ab4ed897af356af5e**. The actual [entry file](https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos550.lean) imports ErdosProblems.Erdos550.Proof, which in turn imports its Main module. The actual [endpoint](https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos550/Main.lean#L80), Erdos550.erdos_550, concerns large trees and multipartite Ramsey numbers. It has parameters k>=2, a monotone sequence of positive part sizes, an eventual n threshold, and a tree T, concluding a Ramsey bound. It has no interval-LCM assertion.

This is a decisive statement mismatch, irrespective of whether the Ramsey proof builds. No audit of the entire Ramsey dependency graph is claimed or necessary to establish that mismatch.

Current PR head: **3ea4d41bf3fb45fb9e522542a09c6ae042c3aebb** in dcdreamy-code/awards, branch plby-jsp-000550. Its actual diff adds nine comment-only Lean pointer files and does not match the body's claim that only catalog fields changed. The [maintainer's 2026-09-23 comment](https://github.com/TheJustinSunPrize/awards/pull/4288#issuecomment-5797719891) requested an external-source replacement submission. State remains open/unmerged. This PR does not establish a solution of JSP-000550.

### #3543: unrelated elementary facts

[PR #3543](https://github.com/TheJustinSunPrize/awards/pull/3543) is closed/unmerged, head **444cb93213541f2864b8581ece5b17efbd9def49**. Its diff's Erdos550.lean proves only primality of 2,3,5,7,11, the sum 2+3+5+7=17, the product 2*3*5*7=210 and 550%3=1. It defines no interval LCM and proves no LCM distinctness theorem. Its catalog pointer used **cb90d20aa346a1a736349163ce5e2fe6ed277a03** in dcdreamy-code/awards. No review comments were returned.

## Number-mismatched awards records

- [#3298](https://github.com/TheJustinSunPrize/awards/pull/3298), closed/unmerged, head **d24d1c427f30a16472a08d545f7cc2f1af07ea17**, labels JSP-000677 as Erdős677 in its body. It cites plby/lean-proofs@8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos677.lean, but that precise path returned 404. Its actual diff again has only elementary primality/sum/product facts and 677%3=2, while editing the totient-preimage catalog entry. It is not a proof of the interval problem.
- [#2412](https://github.com/TheJustinSunPrize/awards/pull/2412), closed/unmerged, head **33400fa5259bf45ebf5e7079a6b7689589bdc3cc**, contains four declarations of True proved by trivial. It supplies no mathematical LCM lemma.
- [#2582](https://github.com/TheJustinSunPrize/awards/pull/2582), closed/unmerged, concerns explicit totient-preimage counts and a different catalog problem. It is not evidence about the LCM conjecture.
- [#3559](https://github.com/TheJustinSunPrize/awards/pull/3559) concerns a separate ratio-of-products problem, JSP-000558. An equal-length keyword match alone is not problem identity.

## Other public Lean and computational work

### rjwalters/lean-genius

The inspected complete file is [Erdos677Problem.lean](https://github.com/rjwalters/lean-genius/blob/470a7df849a5b2c21a8ee06db711561372bc639f/proofs/Proofs/Erdos677Problem.lean) at **470a7df849a5b2c21a8ee06db711561372bc639f**. It defines the correct LCM and full proposition, but does not prove that proposition. Actual implemented scopes include:
- k=1 and k=2 for all starts (lines 221 and 227).
- k=3 for n=0,1,2,3, using native_decide for finite arithmetic.
- A general elementary bound excluding m+k greater than the product of the first interval.
- Basic divisibility, positivity and prime-factorization lemmas.

Line 73 declares the unproved custom axiom thue_siegel_finiteness. The file also uses native_decide. Its metadata acknowledges both that axiom and Lean.ofReduceBool. The k=1,2 and large-m proof terms do not call the custom finiteness axiom in the inspected source; no fresh kernel or transitive-axiom execution is claimed.

Relevant merged PRs include [#15090](https://github.com/rjwalters/lean-genius/pull/15090) (k=1,2), [#18782](https://github.com/rjwalters/lean-genius/pull/18782) (small k=3 starts), and [#25984](https://github.com/rjwalters/lean-genius/pull/25984) (native_decide disclosure). No k=6 theorem occurs in the inspected file.

### qrdlgit/erdos677

[Repository](https://github.com/qrdlgit/erdos677/tree/d64211ecdc02693a11a7bf0468be10f06b6ec48d), sole inspected commit **d64211ecdc02693a11a7bf0468be10f06b6ec48d**, dated 2026-03-31. All seven Lean source files were fetched. The package provides windowLcm, a no-prime-in-second-window lemma, prime-power support and difference divisibility, smoothing of product valuations for p>k, a large/small prime decomposition, and fixed-gap finiteness.

The actual [SylvesterSchur.lean](https://github.com/qrdlgit/erdos677/blob/d64211ecdc02693a11a7bf0468be10f06b6ec48d/RequestProject/SylvesterSchur.lean) leaves general sylvester_schur as sorry; windowLcm_has_large_prime depends on it. The other six files import only Mathlib and Defs, not SylvesterSchur. They are potentially useful prior formalization, subject to a separate exact-version build/axiom review if reused. The package contains no proof of k=6 or of the entire question. The recorded build claims have not been independently replayed in this audit.

### google-deepmind/formal-conjectures

[PR #2946](https://github.com/google-deepmind/formal-conjectures/pull/2946), closed/unmerged, head **952293d9bba216fd45d5376381527906e7ae3a75**, has a title/body suggesting a formally solved known-result variant. The actual diff adds only a statement for m,n<100, with proof literally by sorry; the main statement also remains sorry. This is neither a checked finite certificate nor a proof of the original problem. [Issue #872](https://github.com/google-deepmind/formal-conjectures/issues/872) was a statement-formalization claim; [PR #1235](https://github.com/google-deepmind/formal-conjectures/pull/1235) added the problem statement.

### Other computational or expository records

- [the-omega-institute/trureturing #8768](https://github.com/the-omega-institute/trureturing/pull/8768), merged 2026-09-19, head **ce3b039619e3c378ae9b2720da004ebd9225ad10**, reports a finite scan to N=40000 and k<=24 with zero valid collisions. The unequal-length known examples are explicitly distinguished. This is no universal proof.
- [grandchallenge/MATH-PROGRAMME #1948](https://github.com/grandchallenge/MATH-PROGRAMME/issues/1948#issuecomment-6157157903) records source triage, k=1,2 arguments and a small finite scan, explicitly with no general result.
- [KDDavis91/erdos677-curve-visualisation](https://github.com/KDDavis91/erdos677-curve-visualisation/blob/117a1039ab675ab8c3b8c9bda025080a860b3af1/README.md), commit **117a1039ab675ab8c3b8c9bda025080a860b3af1**, is a k=5, product-ratio 4/3 genus-two visualisation. Its README expressly says supplied rational points are not certified exhaustive and the whole question remains unresolved in that work. Its example at starts 15 and 16 overlaps in four integers. It is not a disjoint-interval counterexample or k=6 solution.

## Audit conclusion and next qualification gate

The inspected records provide no qualifying complete k=6 proof, no valid disjoint equal-length counterexample, and no complete proof of all k. This is a scoped audit conclusion, not an assertion of exhaustive worldwide absence.

A reliable new k=6 theorem would be a fixed-length subresult. It may be published accurately in the author's research repository, but under the inspected awards rules it cannot support an original-problem solution PR or award claim. A genuine k=6 collision satisfying all original constraints would refute the full conjecture and could be prepared for full-solution review.

This audit does not submit an awards PR or claim. The research repository now publishes the partial formalization and a scoped analytic/computational length-six result; its all-length and Lean-completeness boundaries are stated in the current research status. No source scanning, metadata flag, CI claim or unchecked axiom was treated as a full proof.

## Publication recheck, 2026-10-24

GitHub search was repeated across all PR states for JSP-000550, Erdos677, equal-length intervals, and the Formal Conjectures 677 path. The relevant results remained partial or wrong-problem submissions. API checks still show #4846 and #4288 open and unmerged. An additional hit, [awards #2582](https://github.com/TheJustinSunPrize/awards/pull/2582), is closed/unmerged and actually changes the totient-preimage catalog entry; its pinned Erdos677.lean URL currently returns 404, so its Lean theorem type was not independently verified. Its actual catalog diff is unrelated to the LCM problem.

## 2026-10-25 publication refresh

The current all-state source checks found no new qualifying competing proof
or review. The author's [new fixed-length theorem](K6_THEOREM.md) now has
independent rank and saturation certificates; its complete Lean endpoint is
still missing. The all-length requirement, lack of MathDB migration for this
problem, and ineligibility for a whole-problem award submission remain
unchanged. No awards solution PR or award claim has been created.

## 2026-10-25 evening rules and additional prior work

The latest [awards revision](https://github.com/TheJustinSunPrize/awards/tree/c06d67a66a8ba426c68e475eff22ee98a86f4e75)
updates MathDB and renumbers later entries. JSP-000550 and its original-problem
requirements are unchanged. It remains outside the pilot. No whole-problem
solution PR or award claim is justified by this repository's k=6 result.

[HuanHuanHuanFFF/lean-math-lab PR 1](https://github.com/HuanHuanHuanFFF/lean-math-lab/pull/1)
is older work, merged in September 2026 and newly included in this audit.
At full SHA `37e42aca251c33c62cbc2c40f286daa0526d79ee`, the inspected
[RegionConsumer.lean](https://github.com/HuanHuanHuanFFF/lean-math-lab/blob/37e42aca251c33c62cbc2c40f286daa0526d79ee/research/tasks/B677-Lcm/runs/20260908-formalization-92c221/lean/analytic/RegionConsumer.lean)
has the actual theorem `B677Analytic.adopted_regions_noncollision_of_dusart`.
Besides k>0 and n+k<=m, it explicitly assumes `DusartPrimeInterval` and
`m-n<=8*k OR n<=369*k`. The Dusart statement is a hypothesis, not a theorem
proved in that endpoint's source. Its reported finite m<89693 certificate
was not rerun in this audit. The written argument cites an unconditional
prime-interval result, but its frontier still leaves the unbounded region
`n>369*k AND m-n>8*k`. Consequently neither the inspected formal endpoint nor
the written region argument settles all k=6 starts or the full question.
The new [ownership two-factor condition](UNIFORM_STRUCTURE.md) does not reuse
that Lean code or assume its conditional theorem.

Live checks of all states, the three specifically watched awards PRs, the
original discussion and proof-claim pages found no new complete competing
proof or review action. This source inspection does not assert worldwide
absence or mathematical priority.
