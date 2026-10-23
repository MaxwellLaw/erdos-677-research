# Independent k = 6 reduction audit

Author: MaxwellLaw. Research assistance record, 2026-10-23. This document proves reductions only; it does not prove the k = 6 conjecture.

The four-curve reduction is from Payam Danesh and Raoul Bianchetti, [Prime-Power Transport and a Three-Site Reduction](https://ijmttjournal.org/public/assets/volume-72/issue-9/IJMTT-V72I9P101.pdf), Section 8.2. The proofs below were independently reconstructed. This repository contributes a Lean verification of reductions and auxiliary lemmas; it does not claim the reduction as new mathematics.

## Exact product / LCM identity

For n >= 0 put P(n) = (n+1)(n+2)(n+3)(n+4)(n+5)(n+6) and M(n) = lcm(n+1,...,n+6). Define

- e(n) = 0 for n mod 4 in {0,1}, and e(n) = 1 for n mod 4 in {2,3};
- f(n) = 1 for n mod 5 = 4, and f(n) = 0 otherwise;
- g(n) = 12 * 2^e(n) * 5^f(n).

Then P(n) = g(n) M(n).

Proof. For a prime p, v_p(P/M) is the sum of the valuations in the block minus their maximum. For p >= 7 at most one member is divisible by p, so this difference is zero. For p = 5 there are either one or two multiples. There are two exactly when n = 4 mod 5; their quotient by 5 consists of consecutive integers, so their minimum 5-adic valuation is 1. For p = 3 there are exactly two multiples, distance 3 apart. Their minimum 3-adic valuation is exactly 1. For p = 2 there are exactly three even terms. Divide them by 2 to get three consecutive integers. Their valuation sum minus their maximum is 0 when their middle term is even, and 1 when their middle term is odd: in the latter case both endpoint terms are even, differ by 2, and their smaller valuation is 1. Restoring the three factors of 2 and subtracting the maximum restores an additional 2. The middle divided term is odd exactly for n mod 4 in {2,3}. These cover every prime and establish the identity. All terms are positive, so all valuations and divisions used here are defined.

In particular g has period 20 and takes the values 12, 24, 60, 120. P is strictly increasing on the nonnegative integers. Thus, if m > n and M(m) = M(n), then g(m) > g(n), and the reduced ratio g(m)/g(n) is one of 2, 5, 10, 5/2. These are precisely the four pairs (a,b) = (1,2), (1,5), (1,10), (2,5) in a P(m) = b P(n).

## Exact carry filters and sufficiency

Write e_n = e(n), f_n = f(n), and similarly for m. The exact residue filters are:

| (a,b) | e_n,e_m | f_n,f_m |
| --- | --- | --- |
| (1,2) | 0,1 | equal |
| (1,5) | equal | 0,1 |
| (1,10) | 0,1 | 0,1 |
| (2,5) | 1,0 | 0,1 |

These are necessary AND sufficient to have a g(m) = b g(n). Consequently, for n,m >= 0, the product equation together with its exact residue filter is equivalent to M(m) = M(n). No additional valuation condition is needed for this equivalence. Omitting the residue filter gives only a necessary condition. The disjointness constraint remains m >= n+6; it is never dropped in the target theorem.

Set X = 2n+7, Y = 2m+7, U = X^2, V = Y^2 and Phi(T) = (T-1)(T-9)(T-25). Pairing factors gives Phi(X^2) = 64 P(n), and likewise for m. Hence the same four equations are a Phi(V) = b Phi(U). Their original-domain constraints are: X,Y odd, X >= 7, Y-X >= 12, and n=(X-7)/2,m=(Y-7)/2 satisfy the residue filter above. These transformations are polynomial equalities with inverse affine formulas, so no Weierstrass integrality issue arises at this stage. Phi(U),Phi(V) are positive in the original domain.

## Independent nonsingularity proof

The projective closure has equation

a(V-Z)(V-9Z)(V-25Z) - b(U-Z)(U-9Z)(U-25Z) = 0.

At Z=0 its U,V partial derivatives are -3bU^2 and 3aV^2, which cannot both vanish at a projective point. An affine singular point would require Phi-prime(U)=Phi-prime(V)=0. The critical points are r_plus/minus = (35 +/- 8 sqrt(7))/3, and their critical values are (-10240 -/+ 7168 sqrt(7))/27. Both are real and nonzero, with opposite signs (7168^2*7 > 10240^2). If U=V, the curve equation forces a=b; if U and V are the distinct critical points, it contradicts a,b>0. Thus every positive unequal pair (a,b), including all four cases, gives a smooth plane cubic over characteristic zero. Since the cubic contains (U,V)=(1,1), it is a genus-one curve with a rational point. This establishes smoothness without relying on the paper’s computational assertion. It does not determine its integral points.

## The direct square lift has genus ten

One possible alternative is to retain the square conditions directly and study H(X)=Phi(X^2) and a H(Y)=b H(X). For every positive rational a != b, this plane sextic is smooth. Indeed, H-prime(T)=2T Phi-prime(T^2), so its critical values are exactly -225 and the two values (-10240 -/+ 7168 sqrt(7))/27 above. The latter two have opposite signs. The only distinct pair with the same sign consists of -225 and the negative irrational critical value; their ratio is irrational, and hence cannot equal a positive rational coefficient ratio. Equal critical values would force a=b. At infinity the X,Y partial derivatives of the leading form aY^6-bX^6 cannot vanish simultaneously. A smooth plane sextic has genus (6-1)(6-2)/2=10.

This does not prove that there are no admissible rational or integral points. It explains why imposing both square conditions before solving the genus-one integral-point problem leads to a substantially different high-genus problem. No complete Chabauty, Mordell-Weil sieve, or covering computation has been performed here.

## Gcd restriction: independently rederived, already present in Proposition 25

The base restriction below is the k=6 instance of Danesh--Bianchetti, p.28, Proposition 25, equations (250) and (254). The proof was rederived independently here, but this is NOT a new mathematical contribution.

Let d = gcd(X,Y) for an integral solution of a Phi(Y^2) = b Phi(X^2), and D=b-a. Since Phi(T) = T^3 -35T^2+259T-225, reduction modulo d^2 gives 225 D = 0 mod d^2. Hence

d^2 divides 225(b-a).

For the four pairs, and because X,Y are odd, this implies d divides 15,15,45,15 respectively before carry filtering.

The carry filters sharpen this substantially. In each of the last three branches f(n)=0 and f(m)=1, equivalently 5 does not divide X and 5 divides Y, since X=2n+7. Hence 5 does not divide d. The exact LCM-carry restrictions therefore give, in pair order:

- (1,2): d divides 15;
- (1,5): d divides 3;
- (1,10): d divides 9;
- (2,5): d divides 3.

Furthermore, for the paper’s slope gcd h=gcd(bX-aY,Y-X), put D=b-a. The elementary gcd identity gives h=gcd(DX,Y-X). This h divides both DX and DY, and therefore divides D*gcd(X,Y)=D*d (for example, by Bezout). Combining the above exact carry restrictions yields:

| (a,b) | d divides | h divides | Paper Theorem 26 bound for h |
| --- | --- | --- | --- |
| (1,2) | 15 | 15 | 15 |
| (1,5) | 3 | 12 | 960 |
| (1,10) | 9 | 81 | 10935 |
| (2,5) | 3 | 9 | 405 |

These explicit lists are direct consequences of the existing Proposition 25 combined with the existing carry formula (23). We did not find the exact four lists printed in the paper, but the ingredients and structural argument are already there. The last table column quotes only the weaker bound displayed in Theorem 26; it must not be read as the strongest bound available from the paper. The contribution here is explicit specialization and formal verification, not a new gcd-descent theorem. These restrictions do not bound X or Y, do not exclude all points, and do not solve k=6.

## Why a finite congruence-only exclusion cannot finish this route

For the first three pairs, the negative integer root pairs (n,m)=(-3,-2),(-2,-1),(-3,-1) have P(n)=P(m)=0 and have exactly the required g ratios 2,5,10. For any fixed modulus Q, take the same residues modulo lcm(Q,20), then add sufficiently large independent multiples of this modulus to make n>=0 and m>=n+6. The product equations and all carry filters continue to hold modulo Q. These are NOT actual LCM collisions; they prove that no finite-modulus test of just these equations and carry filters can exclude every positive disjoint pair.

The same phenomenon holds for (2,5). Decompose a multiple of 20Q into its 2-primary, 5-primary, and prime-to-10 parts. Choose n=-2 on all three parts. Choose m=-3 on the 2-primary part, m=-1 on the 5-primary part, and m=-1 on the prime-to-10 part. The Chinese remainder theorem gives simultaneous residues. Both P(n) and P(m) vanish modulo Q, while e(n)=1,e(m)=0,f(n)=0,f(m)=1. Positive disjoint representatives again exist. Consequently all four branches survive every finite set of purely congruence tests. An effective global bound, integral-point completeness argument, or other global arithmetic input is required.

This obstruction addresses the product equations and carry filters, not every conceivable congruence argument augmented by auxiliary variables, descent, nonzero conditions or global bounds.

## Status

Verified independently: product/LCM defect; the four coefficient pairs and their completeness; exact necessary-and-sufficient residue filters; original-domain boundary constraints; nonsingularity; the gcd-square divisibility above; obstruction to a finite congruence-only exclusion.

Unresolved: complete integral-point computation with square and carry conditions; a certified effective upper bound; complete k=6 noncollision or a counterexample; the all-k problem. No finite search is used as a nonexistence proof, and no CAS claim of completeness is made.
