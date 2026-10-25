# Fixed sources and audit status

Audit dates: 2026-10-23–24 (Asia/Shanghai). Sources and submission states were rechecked immediately before the initial public release. No global priority claim is made.

| Source | Fixed version or content hash | Observed status |
| --- | --- | --- |
| [awards](https://github.com/TheJustinSunPrize/awards/tree/5b7126acf3d3d31c71e5964525807d1532cba892) | `5b7126acf3d3d31c71e5964525807d1532cba892` | Catalog, templates, verification, attribution, award process and MathDB pilot checked. JSP-000550 remains open, Lean No, Eligible No; not in the pilot. |
| [Formal Conjectures, initial snapshot](https://github.com/google-deepmind/formal-conjectures/blob/ac02cd5f50407650b37344083b7c1f0f4ed1f96c/FormalConjectures/ErdosProblems/677.lean) | `ac02cd5f50407650b37344083b7c1f0f4ed1f96c` | Exact quantified problem has `by sorry`. Lean and mathlib dependencies were pinned from this revision. |
| [Formal Conjectures, publication recheck](https://github.com/google-deepmind/formal-conjectures/blob/dbc2db9ee32219c8c1e26db64b2b7f3ed7b33324/FormalConjectures/ErdosProblems/677.lean) | `dbc2db9ee32219c8c1e26db64b2b7f3ed7b33324` | Same problem file blob `303699d56147eb8edd96b0c493dd2b1e53af23e3`; no full proof added. |
| [Danesh and Bianchetti 2026](https://ijmttjournal.org/public/assets/volume-72/issue-9/IJMTT-V72I9P101.pdf) | SHA256 `99f3db586d45c66f87280a78466b191892a030ef4577309297acd6061aab5f3f` | Section 8.2 explicitly leaves k=6 unresolved. Four coefficients, product identity and smoothness independently checked. |
| [Erdős, Mathematics Magazine 52 (1979), 67–70](https://www.renyi.hu/~p_erdos/1979-22.pdf) | SHA256 `772e2f84dff324b363dc6fbb74a9449f36c42569027b29efb3b71af84ff18964` | The site's p.67 source; visual inspection confirms the equal-length conjecture includes m>=n+k. |
| [Erdős, Acta Math. Acad. Sci. Hungar. 33 (1979), 71–80](https://users.renyi.hu/~p_erdos/1979-23.pdf) | SHA256 `a4703a104adcbbde0ed605c9ff81379adee8b7ceda3714ea455b5b68ae720dfd` | A different same-titled paper, cited by Danesh–Bianchetti; p.78 also includes m>=n+k. |

The [original problem](https://www.erdosproblems.com/677), [all eight discussion comments](https://www.erdosproblems.com/forum/thread/677), and [proof-claims page](https://www.erdosproblems.com/forum/thread/677/proof-claims) were successfully read in a browser after direct requests returned 403. The page reported last edited 30 September 2025, zero proof expositions and zero proof claims; the latest discussion post was 2 April 2026. The comments link qrdlgit's partial formalization and explicitly distinguish fixed-gap finiteness from the already known fixed-length finiteness. Neither is a solution of k=6. The adjacent solved Problem #678 is different.

## Verified

The original equal-length, disjoint, positive-integer conditions; exact carry factor; the four coefficient pairs; equivalence when carry conditions are retained; no denominator or zero-factor issue in the centered product transformation; smoothness of the four plane cubics by an independent critical-value argument; failure of a naive Weierstrass-integral-point replacement; actual scopes of the examined third-party submissions. The carry-refined gcd bounds directly specialize the paper's Proposition 25; they are not a new structural descent theorem.

## Still unverified or unresolved

The journal paper's full historical search and supplementary computations have not all been independently reproduced. Their finite reported ranges are not new results here. The later [k=6 proof chain](K6_THEOREM.md) supplies effective bounds, complete target-domain exclusion, and independent group certificates. It supplies no complete Lean k=6 endpoint or all-length result. Historical Magma rank/basis flags are cross-checks, not assumptions of the later independent proof. The inaccessible primary-text hypotheses noted in the [detailed source audit](../cas/SOURCE_AUDIT.md) and [Farhi–Kane / Saradha–Shorey supplement](../cas/LITERATURE_SUPPLEMENT.md) are not used as mathematical premises.

## Errors found in examined claims

The [prior-work report](PRIOR_WORK.md) documents wrong-problem submissions and finite closed computations advertised as full results. A later research page's claim that Erdős originally required the strict inequality m>n+k conflicts with both visually inspected equal-length statements; OCR confused that symbol with the subsequent different-length extension. These are source and scope findings, not evidence that this repository solves the problem.

## 2026-10-25 source refresh

The original problem/forum still had eight comments, zero proof claims and zero
expositions when checked. Awards remained at
`5b7126acf3d3d31c71e5964525807d1532cba892`; JSP-000550 was still outside the
MathDB pilot. Formal Conjectures advanced to
`37f0808b83c56c8cef4ea5816b8329c09b8905a8` via an unrelated Brennan change.
No new qualifying competing solution or external review was found in the
recorded all-state searches. This is a scoped source audit, not a claim of
worldwide priority.

For the independent rank proof, the inspected CFOSS *Explicit n-Descent III*
PDF at the linked author site has SHA256
`c2fd51b9b0fe6aab25114b98d9cce48846c351e555395c87aed4bd1b659ff5b1`.
Milne *Algebraic Number Theory*, version 3.08 (19 July 2020), supplies the
Minkowski and S-unit theorems cited in the ideal-certificate notes. Third-party
PDFs are linked and attributed, not vendored into this repository.

## 2026-10-25 evening refresh

Awards advanced via [merged PR 5135](https://github.com/TheJustinSunPrize/awards/pull/5135)
to `c06d67a66a8ba426c68e475eff22ee98a86f4e75`. The current templates,
contribution/claim rules, verification and attribution instructions, and both
MathDB registers were read. The renumbering affects later catalog entries;
JSP-000550 remains Erdős #677, with unchanged catalog blob
`1adf510bd9492acb7caf72ffc7c29900be1f45c8`, Open / Lean No / Eligible No.
It is still outside the MathDB pilot and still requires a complete original
solution. The update supplies no new eligibility for this fixed-length work.

Formal Conjectures advanced to `49ba26bac3212084999860c575fcc70af42b3128`;
its 677 blob remained `303699d56147eb8edd96b0c493dd2b1e53af23e3`.
The original problem, forum and proof-claim pages were read in a browser
again after direct HTTP returned 403: eight comments, latest post5214 on
2 April 2026, zero proof expositions and zero claims. Posting remained suspended.
The original research repository had successful CI and no external review or
PR. Twelve all-state updated-since searches returned no new relevant item,
with incomplete_results=false; this is scoped search evidence only.

An older HuanHuanHuanFFF submission was newly added to the scope audit;
[PRIOR_WORK.md](PRIOR_WORK.md) records its explicit Dusart hypothesis and
unbounded remaining region. It is not a competing complete k=6 or all-length
endpoint in the inspected source. No third-party build is claimed.
