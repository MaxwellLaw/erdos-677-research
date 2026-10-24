# Source audit for Erdős #677 / JSP-000550

Audit performed 2026-10-23–24, Asia/Shanghai. This record distinguishes sources and mathematical scope. It does not certify a full solution.

## Verified

- The fixed target is equal-length, disjoint intervals of positive integers, with `n>=0`, `k>=1`, `m>=n+k`. This is Erdős #677; Erdős #550 is a different problem.
- Two distinct 1979 Erdős papers have the same title, “Some unconventional problems in number theory.” The [Mathematics Magazine 52(2), 67–70 paper](https://www.renyi.hu/~p_erdos/1979-22.pdf), item 2 on printed page 67, is the source corresponding to `[Er79,p.67]`. The [Acta Math. Acad. Sci. Hungar. 33, 71–80 paper](https://users.renyi.hu/~p_erdos/1979-23.pdf), printed page 78, is the source cited in the 2026 paper. Both scans were inspected visually. Their equal-length conjecture includes `m>=n+k`.
- The first Mathematics Magazine inequality is a slanted non-strict symbol that OCR/search text wrongly turns into `>`. Its following *different-length* extension does use strict `>`. Neither OCR nor the shared title suffices to identify the quantifiers.
- [Danesh–Bianchetti 2026](https://ijmttjournal.org/public/assets/volume-72/issue-9/IJMTT-V72I9P101.pdf), Section 8.2, explicitly leaves k=6 unfinished. It lists four cubic equations plus square and carry restrictions. Independent exact birational maps and denominator checks are in `CAS.md`.
- That paper's reported search region is `1<=k<=150`, `0<=n<m<=150000`; it reports no disjoint collision. This is finite evidence, not nonexistence for every start. The full reported search was not rerun in this audit.
- Proposition 25 already contains `c^2 | 225(b-a)` for k=6 and `c | h | (b-a)c`. Equation (274) separately gives `h | 15(b-a)^3`. The more specific carry-refined bounds are not explicitly listed there. Specializing these known ingredients must be attributed as a refinement, not assumed globally original.

## Live problem and forum check

- Direct HTTP and search-tool requests to the main problem and forum returned 403, but a browser successfully loaded the main page, all eight discussion comments, and the proof-claims page on 2026-10-24 (Asia/Shanghai). The page stated last edited 30 September 2025, showed zero proof expositions and zero proof claims, and the latest discussion comment was dated 2 April 2026. No complete k=6 proof appeared in those comments. This is an observed snapshot, not a guarantee against later or elsewhere-published work.

## Unverified or incomplete

- The 2026 paper names computational scripts but the inspected PDF and journal landing page did not provide a retrievable supplementary-code location. Its complete claimed computation tables therefore remain unreplicated here.
- The paper's Saradha–Shorey reference was identified, but its full primary text was not obtained. Its abstract cannot establish which ratio theorem hypotheses apply to this problem. No theorem from that inaccessible text is used in this work.
- Targeted searches for a completed k=6 proof or stronger explicit scale tables did not locate one. This is a record of search results, not a guarantee that no competing proof exists.
- Full-basis Magma flags and exact map identities do not determine all integral points of the original cubics. The subsequent effective lower-bound, exact lattice-distance certificates and residual enumeration are now specified in `global-bound/README.md`. Full-group coverage still uses external Magma certification, and the analytic/computational chain is not Lean verified.

## Correction recorded during this audit

The [July 2026 research page](https://www.erdosproblemaday.com/day/677-lcm-bridge) describes the equal-length source condition as strict and calls the adjoining boundary an extension. The primary scans already include the boundary. This discrepancy was checked from the images, not from OCR. During the audit, discovering the second same-titled source briefly led to an OCR-based hypothesis that the two papers differed; the image check rejected that hypothesis. No public mathematical claim was based on that temporary hypothesis.

The July page itself does not claim to close k=6. Its overlapping examples cannot disprove the stated disjoint-interval conjecture.

## Fixed local source versions

The source PDFs are retained locally for audit and are **not redistributed** in this original-code publication set.

| Source | SHA-256 |
|---|---|
| Danesh–Bianchetti, IJMTT-V72I9P101.pdf | `99f3db586d45c66f87280a78466b191892a030ef4577309297acd6061aab5f3f` |
| Erdős, Mathematics Magazine 1979-22.pdf | `772e2f84dff324b363dc6fbb74a9449f36c42569027b29efb3b71af84ff18964` |
| Erdős, Acta 1979-23.pdf | `a4703a104adcbbde0ed605c9ff81379adee8b7ceda3714ea455b5b68ae720dfd` |
| Stroeker–de Weger, Acta Arith. 87 (1999), 339–365 | `650510eaed255fd0cdaab9497951f20a6a1408a90cc0e67c922069059e1d9a1c` |
| Chern, arXiv:1412.6736v2 | `d8cda5becdefc9445f720811dd4159bb6a9aeedae6f507ea09118419223d49a8` |
| Chern, program appendix | `6b6ae4fd85739a60658255dd8ddc43a6c72bc9bdfcc2ece166189214a15a741a` |

| Additional inspected source | SHA-256 |
|---|---|
| David, Mémoires SMF 62 (1995) | `aefffcbf1d8475a4f17ce95a0de0240db687a9108d0ced5d8d972c844dc504ae` |
| Tzanakis, Acta Arith. 75 (1996), 165–190 | `00beb2e622143f0847590c85ca4adf07fecfb380468d68dc77e6f70ff7a203ff` |
