# Independent algebraic certificates

Let `f(T)=T³+a2 T²+a4 T+a6`, and set `K=Q(theta)` with `f(theta)=0`.
Let `S_Q` be the displayed rational-prime set, and `S_K` all prime ideals above
it. Write `Cl_S` for the ideal class group after inverting `S_K` and

```
K(S,2) = {alpha in K*/K*² : v_P(alpha) is even for every P outside S_K}.
```

All vector coordinates in the raw ideal relations are relative to the displayed
integral basis, not automatically the power basis `1,theta,theta²`.

| Ratio | (a2,a4,a6) | disc(K) | S_Q | #S_K | dim Cl/2 upper | dim Cl_S/2 upper | norm-kernel dimension upper |
|---|---|---:|---|---:|---:|---:|---:|
| (1,2) | (-1,-65,261) | -11948 | {2,3} | 4 | 1 | 0 | 3 |
| (1,5) | (-1,-408,6912) | -67175 | {2,3,5} | 7 | 0 | 0 | 5 |
| (1,10) | (1,-1633,97763) | -3340300 | {2,3,5} | 4 | 1 | 1 | 3 |
| (2,5) | (1,-1633,32963) | -1590700 | {2,3,5} | 4 | 1 | 1 | 3 |

## Maximal orders

`verify_export_algebra.py` proves each cubic irreducible by reduction modulo
11, 7, 7, 37, respectively. It computes multiplication and traces directly in
the rational quotient algebra. The displayed bases contain 1 and are closed
under multiplication; their trace discriminants are exactly those in the table.
Their indices over `Z[theta]` are 6, 120, 270, 90.

To prove maximality, suppose an order `O` is properly contained in `O_K`. Some
prime `p` divides the finite index. The discriminant-index identity implies
`p² | disc(O)`, and the finite group `O_K/O` has an element of order `p`. Thus
some nonzero coset of `(1/p)O/O` has an integral representative. Integrality is
unchanged by adding an element of `O`. The checker enumerates every such coset
and evaluates the characteristic-polynomial coefficients

```
-Tr(v), (Tr(v)²-Tr(v²))/2, -Norm(v).
```

An algebraic element is integral exactly when its characteristic polynomial
over Q is monic with integer coefficients. Every candidate has a nonintegral
coefficient. The only possible primes are 2 and 5; the tested counts are 7;
124; 7+124; and 7+124. Therefore the four orders are maximal. This proof uses
exact arithmetic, not the meaning of Magma's `MaximalOrder` label.

## Unit squareclasses

The checker verifies that the two exported unit candidates are integral and
have norm ±1. The first is -1. `verify_unit_squareclasses.py` gives the following
witnesses for the other unit `u`:

| Case | Prime p | theta mod p | u mod p |
|---|---:|---:|---:|
| 1 | 5 | 2 | 2 |
| 2 | 29 | 7 | 10 |
| 3 | 13 | 9 | 7 |
| 4 | 13 | 8 | 7 |

Each denominator is a p-adic unit, each listed root satisfies `f`, and Euler's
criterion gives Legendre symbol -1 for `u`. Because `p=1 mod 4`, -1 has symbol
+1. Neither `u` nor `-u` can be a square in K: a square root would have valuation
zero at this residue map and reduce to a square. Each field has signature
(1,1), so its unit group is `{±1}` times a free rank-one group. By Dirichlet's
theorem the classes of `-1,u` therefore form the complete unit group modulo
squares. This does not establish that `u` is a fundamental unit, which is not
required. The rank bound below uses the S-unit rank rather than this explicit
unit basis.

## Complete ideal generators and exact relations

Minkowski's bound for a cubic field of signature (1,1) is
`8*sqrt(|disc(K)|)/(9*pi)`. Since `pi>3`, the verified integer inequalities
`(27B)² >= 64|disc(K)|` show that every ideal class has an integral representative
of norm at most the chosen values `B=33,77,542,374`. Factoring those ideals shows
that prime ideals of norm at most B generate the class group.

For **every rational prime p<=B**, the raw file lists a decomposition of `pO`.
The independent checker verifies all of the following:

1. Each ideal matrix is an integral full-rank lattice closed under multiplication
   by the order basis, and it contains `pO`.
2. The quotient is a field. It computes the quotient as an F_p vector space and
   exhibits an element with irreducible characteristic polynomial of the full
   quotient dimension. That dimension is at most three; degree-two and
   degree-three irreducibility is checked by testing every possible root.
3. The ideals above p are distinct and their products with the recorded
   exponents equal `pO` exactly. Unique factorization in the verified maximal
   order then proves these are all primes above p, with no missing factors.

Every ideal of norm at most B lies above one of these rational primes. The
numbers of rational primes, prime ideals, and required principal relations are:

| Case | Rational primes | Prime ideals | Principal relations |
|---|---:|---:|---:|
| 1 | 11 | 19 | 13 |
| 2 | 21 | 37 | 21 |
| 3 | 100 | 182 | 100 |
| 4 | 74 | 136 | 80 |

For every prime ideal `P_i` of norm at most B, the certificate supplies an
algebraic integer `alpha_i` and verifies exactly

```
P_i^h * P_anchor^(h*b_i) = (alpha_i),   b_i in {0,1},
```

where `h=1,27,3,3`, respectively. When there is no anchor, every `b_i` is zero.
All ideal arithmetic is performed as integer lattices using Euclidean row
operations for Hermite normal form; all principal ideals are generated by the
three products `alpha_i*b_j` with the order basis. The verifier compares the
resulting lattices exactly. It does not merely compare ideal norms.

Since h is odd, reducing these relations modulo twice the class group expresses
every class as a multiple of the anchor. Case 2 has no anchor, so its mod-2
class group vanishes. Case 1's anchor is above S_Q, so its S-class group modulo
2 also vanishes. In cases 3 and 4 the anchor need not be above S_Q, and the
upper bound is one. No exact class number or lower bound is needed.

## Norm-square dimension

The elementary ideal-factorization sequence is

```
0 -> O_{K,S}*/O_{K,S}*² -> K(S,2) -> Cl_S[2] -> 0.
```

Indeed, outside S write `(alpha)=a²`; send alpha to the class of a. Multiplying
alpha by a square changes a by a principal ideal. A trivial class gives an
S-unit after dividing by a square, and every 2-torsion class has such a
representative. For a finite abelian group, `dim Cl_S[2]=dim Cl_S/2Cl_S`.
The S-unit theorem, signature (1,1), and torsion `{±1}` give

```
dim K(S,2) = 2 + #S_K + dim Cl_S[2].
```

The norm map has rank at least `1+#S_Q`. The rational elements `-1` and each
`q in S_Q` lie in K(S,2), and their norms are `-1` and `q³`; their squareclasses
in Q are independent. Subtraction gives the upper bound

```
1 + #S_K - #S_Q + dim Cl_S[2] = 3,5,3,3.
```

This is a theorem about the four global squareclass spaces. To bound elliptic
ranks one must also prove that the elliptic Kummer image lies in the stated
norm kernel and, in case 2, apply the additional local condition. Those steps
are not hidden assumptions of the ideal checker.

## Sources and trust boundary

[J. S. Milne, Algebraic Number Theory](https://www.jmilne.org/math/CourseNotes/ANT.pdf),
version 3.08 (19 July 2020), Theorems 4.3–4.4, 5.1 and 5.11 supply Minkowski's
bound, class-group finiteness, and the ordinary/S-unit ranks. The short ideal
sequence and the norm-rank argument are justified above. The arithmetic
certificates were generated from Magma witnesses, but their validity uses no
Magma class-number, Selmer-dimension, or full-basis flag.

The [official Magma class-group documentation](https://magma.maths.usyd.edu.au/magma/handbook/text/416)
describes the relation method and distinguishes Minkowski verification from
conditional bounds. The discovery script explicitly used `Proof:="Full"`;
this setting is additional provenance, not part of the independent proof.
The [p-Selmer documentation](https://magma.maths.usyd.edu.au/magma/handbook/text/436)
defines K(S,p) and warns that applying its class map to unsupported elements
does not verify their support; this package therefore checks concrete ideals
instead of trusting such a call.

The logical algebraic-number-theory arguments in this document and the Python
arithmetic are not Lean formalizations. No claim about a complete solution of
the original all-length problem follows from this certificate.
