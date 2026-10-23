# Additional source audit — 2026-10-24 (Asia/Shanghai)

This is an attribution and applicability audit. It does not solve the length-six problem. Third-party PDFs and source archives are retained locally for research and are not intended for redistribution with our original code.

## Farhi–Kane: the period and valuation formula are prior mathematics

Bakir Farhi and Daniel Kane, *New results on the least common multiple of consecutive integers*, Proc. Amer. Math. Soc. **137** (2009), 1933–1939, [DOI 10.1090/S0002-9939-08-09730-X](https://doi.org/10.1090/S0002-9939-08-09730-X). The [arXiv record](https://arxiv.org/abs/0808.1507v1) dates v1 to 2008-08-11. The author's [UCSD PDF](https://cseweb.ucsd.edu/~dakane/lcm.pdf) is also linked in the Erdős #677 discussion.

Frozen versions downloaded from official arXiv endpoints:

| Artifact | Endpoint | SHA256 |
|---|---|---|
| 8-page PDF, 183903 bytes | `https://arxiv.org/pdf/0808.1507v1` | `4b572dce7a786c90ee888bab1fa14f37da24f5ab1add332b2625457f08242951` |
| compressed TeX, 6733 bytes | `https://arxiv.org/src/0808.1507v1` | `f5fee9a55d6d17c70202112ada0e769fd46836c8ccdf3930ddf8e12eb41751b3` |

The downloaded PDF's custom font encoding degraded local text extraction. The following statements were checked against the official decompressed TeX source, in addition to readable web extraction. The TeX is Latin-1 encoded; the archive contains gzip-compressed TeX, not a tar archive.

Their function `g_k(t)` is the product of **k+1** terms from `t` through `t+k`, divided by their LCM. Consequently our length six corresponds to their `k=5`, with `t=n+1`.

Theorem 3.2 (PDF p. 6, TeX label `mainthm`) gives the exact period. For a prime `p≤k`, let `e=max_{1≤i≤k} v_p(i)`. Its contribution to the period is `p^e` when `v_p(k+1)<e`, and 1 otherwise. Equation (12) (PDF p. 7, TeX label `gpkformula`) expresses `v_p(g_k(t))` as the sum, for `1≤j≤e`, of the number of multiples of `p^j` in the block minus 1. Lemma 3.1 supplies the disappearing-prime case; Theorem 2.5 supplies the other case.

Here is our direct specialization, not a novelty claim. For six terms:

- `p=2`: `e=2` and `v_2(6)=1`, so the period retains 4.
- `p=3`: `e=1` and `v_3(6)=1`, so it removes 3.
- `p=5`: `e=1` and `v_5(6)=0`, so it retains 5.

Thus the exact period is **20**, not merely a conjectured or experimentally observed period.

Put `D(n)=∏_{i=1}^6(n+i)/M_6(n)`. Counting the multiples gives

`v_2(D(n)) = 2 + [n mod 4 ∈ {2,3}]`,

`v_3(D(n)) = 1`,

`v_5(D(n)) = [n mod 5 = 4]`,

and zero at every other prime. Therefore

`D(n)=12·2^[n mod 4 ∈ {2,3}]·5^[n mod 5 = 4] ∈ {12,24,60,120}`.

The normalized carry is `D(n)/12`. Its four possible values and period are immediate instances of prior work. Distinct increasing blocks have increasing positive products. Their equal-LCM condition consequently forces an increasing ratio of carry values; reducing the six possible ratios among `{1,2,5,10}` gives `{2,5,10,5/2}`. These are the four cubic coefficient branches already reported in the 2026 paper. Our contribution is independent derivation, exact scope checks, and the new Lean implementation, not discovery of the period or of these branches.

## Saradha–Shorey: full-text access remains incomplete

N. Saradha and T. N. Shorey, *On the ratio of two blocks of consecutive integers*, Proc. Indian Acad. Sci. (Math. Sci.) **100** (1990), 107–132, [DOI 10.1007/BF02880956](https://link.springer.com/article/10.1007/BF02880956). The publisher record confirms receipt 1989-12-08, revision 1990-05-20, and August 1990 issue date.

The publisher abstract states finiteness under additional assumptions, which it does not spell out. Its special case `a=b=1, l=k` concerns unequal block lengths `k` and `2k`, not our equal-length case. The reported solution `x=7,y=0,k=3` checks as `8·9·10=1·2·3·4·5·6`.

Actual retrieval outcomes:

- The publisher supplied a subscription preview; a direct content/PDF endpoint also returned HTML, not a PDF. No full-text or theorem verification is claimed from that response.
- IAS's official `https://www.ias.ac.in/article/fulltext/pmsc/100/02/0107-0132` and legacy `https://www.ias.ac.in/public/Volumes/pmsc/100/02/0107-0132.pdf` returned 403 to the research clients. Browser navigation to the former timed out; a subsequent observation was blocked by an open extension UI.
- The indexed [IAS repository record](https://repository.ias.ac.in/67750/) gave metadata and the abstract in search results, but direct Chrome access returned 404.
- [ResearchGate](https://www.researchgate.net/publication/225161489_On_the_ratio_of_two_blocks_of_consecutive_integers) identifies an author-uploaded public full text by N. Saradha, uploaded 2014-04-23. The research client did not retrieve it; Chrome displayed a security-check gate, which was not completed. Thus we do not say that no author copy exists.

An accessible source by a close collaborator gives a useful applicability check, explicitly distinguished from reading the original proof: R. Tijdeman, *Highlights in the Research Work of T. N. Shorey*, in *Diophantine Equations*, ed. N. Saradha, TIFR/Narosa (2007), [author PDF](https://pub.math.leidenuniv.nl/~tijdemanr/shoreyt.pdf), §10, printed p. 13 (= PDF p. 13). Downloaded 175039-byte PDF SHA256: `30c1ea2584b12a7dbefcd7296bfb9c7c6fc1284e6e5106ea080302af99cc5677`.

That account attributes to the 1990 paper finiteness when **the starting integers x,y are composed of fixed primes**, and a separate bound `x−y ≥ C·x^(2/3)` with `C>0` depending on the coefficients. It describes the equation as

`A·x(x+1)…(x+k−1) = B·y(y+1)…(y+k+l−1)`.

For our branch take `x=m+1, y=n+1, A=a, B=b, k=6, l=0`. Restricting the prime factors of **a,b** to `{2,5}` does not establish any fixed-prime support for **x,y**. The cited finiteness hypothesis cannot simply be applied. The gap lower bound alone also gives no finite upper bound on the starts. No effective, numerically specified bound or classification covering our four length-six cases was obtained from this source.

A further promising reference is T. N. Shorey, *On the ratio of values of a polynomial*, Proc. Indian Acad. Sci. (Math. Sci.) **93** (1984), 109–116, [DOI 10.1007/BF02840654](https://link.springer.com/article/10.1007/BF02840654). Its abstract specifically names equal-length product ratios, but only a publisher preview was retrieved. Its exact hypotheses and effectiveness remain unverified. It is a research entry point, not an input to our proof.

No theorem in the Lean reduction depends on either unverified Saradha–Shorey/Shorey paper. Obtaining the 1990 and 1984 full texts remains an open source-audit task; the present record does not assert that these papers cannot contain other useful results.
