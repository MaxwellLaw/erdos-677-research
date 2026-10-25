# A local-3 restriction for the (1,5) cubic

Author: MaxwellLaw. Exact arithmetic checkpoint, 2026-10-25 UTC.

The author, MaxwellLaw, used AI as an assistive tool.

Let E be y²=f(x), where f(t)=t³-t²-408t+6912, and let
K=Q(theta), f(theta)=0. Put S={2,3,5}. Define V to be the subgroup of
K*/K*² with even ideal valuations outside primes over S and square rational
norm. The accompanying certificate constructs four members of V whose
images in (Q3*/Q3*²)^3 are linearly independent over F2. No Selmer-group
output or CAS completeness flag is assumed.

## Four integral witnesses

Set w=(theta²+71theta+24)/120. Exact multiplication in Q[t]/(f) verifies
w³-8w²-27w+1314=0, so w is an algebraic integer. The polynomial f has no
root modulo 7, hence is irreducible over Q. All coordinates below are
integers in the basis (1,theta,w):

| i | alpha_i coordinates | norm |
|---|---|---|
| 1 | (-551,193,-217) | -2^27 |
| 2 | (-154,174,-221) | -2^27 |
| 3 | (-3319,-403,738) | -2^27 |
| 4 | (48923,-2238,11240) | -3^27 |
| 5 | (-337191,-127534,308272) | 3^27 |
| 6 | (-685039,-116204,241024) | -3^27 |

The four witnesses are
beta1=alpha1*alpha2, beta2=alpha1*alpha3,
beta3=-alpha4*alpha5, beta4=alpha4*alpha6.
Their exact norms are respectively 2^54,2^54,3^54,3^54. The script
checks these by determinants of the rational multiplication matrices.
They are integral elements with norm supported on S. Thus every prime
ideal outside S has valuation zero in each principal ideal (beta_i):
no class-group or ideal-factorization assertion is required for this
membership check. Their norms are squares, so all four belong to V.

The alpha_i candidates came from the Magma discovery output
../class_s_relations_2.result.json. Only their explicit
integer coordinates are reused. Their integrality, norm, S-support
consequence and local images are checked independently of that output's
principal-ideal claims. The certificate includes an unused seventh
S-supported alpha as provenance; it is not needed by the rank-four argument.

## Three exact 3-adic embeddings

Use seeds r=0,6,1. The pairs
(v3(f(r)),v3(f'(r))) are (3,1),(3,1),(1,0).
The three root neighborhoods 0+9Z3, 6+9Z3, and 1+3Z3 are disjoint.

The script constructs roots digit by digit. Write s=v3(f'(r)), start
with k=s+1, and maintain f(r)=0 modulo 3^(k+s).
Among r, r+3^k and r+2*3^k, precisely one makes f vanish modulo
3^(k+s+1). This follows from Taylor expansion:
the linear coefficient f'(r)/3^s is a unit, and higher terms vanish
modulo 3^(k+s+1) since k>=s+1. The derivative valuation stays s.
Induction supplies a Cauchy sequence with a unique root in the initial
neighborhood. The saved residue therefore equals that root modulo
3^80. This is an exact Hensel certificate, with no floating-point p-adic
precision claim. Since there are three distinct roots of a cubic,
K tensor Q3 is Q3^3.

For the general lifting theorem, see Milne, Algebraic Number Theory
v3.01, Newton's Lemma 7.32:
https://www.jmilne.org/math/CourseNotes/ANT301.pdf
The explicit digit induction above also proves the particular precision
bound used here.

To evaluate beta=A(theta)/d, use integer A and d>0. Since the actual
root and saved residue differ by a multiple of 3^80, the numerator
evaluations agree modulo 3^80. Every observed numerator valuation is
strictly below 80. The exact valuation v3(A(r))-v3(d) and the unit
modulo 3 after stripping these powers are consequently determined.
Denominators divisible by 3 are stripped before inversion; they are
never inverted modulo a power of 3.

## Local squareclasses and independence

A nonzero Q3 element has squareclass determined by the parity of its
valuation and whether its unit is 1 or 2 modulo 3. Units congruent to 1
are squares by Hensel lifting, while 2 is nonsquare. Thus encode each
embedding by two bits (valuation parity, unit minus 1), in seed order
(0,6,1). The four exact rows are

```
beta1 : 0 1 | 0 1 | 0 0
beta2 : 0 0 | 0 1 | 0 1
beta3 : 1 1 | 1 0 | 0 1
beta4 : 1 1 | 0 0 | 1 1
```

The last two rows have independent valuation projections (1,1,0) and
(1,0,1). The first two have zero valuation projections and independent
unit projections (1,1,0) and (0,1,1). This proves rank four directly;
the script also checks rank by binary elimination.

## Consequence for the local descent condition

Because all three roots are in Q3, E(Q3)[2] has four elements.
An open subgroup U of E(Q3) has multiplication by 2 bijective; one may
take the formal subgroup E1(Q3). This holds without good reduction,
since 2 is prime to 3. See Milne, Elliptic Curves, second edition,
Chapter II, Corollary 4.2(a), printed p.64:
https://www.jmilne.org/math/Books/EC2.pdf

For the finite abelian group A=E(Q3)/U, bijectivity of [2] on U gives
E(Q3)/2E(Q3) = A/2A and E(Q3)[2] = A[2]. A finite abelian group has
equally many elements in A[2] and A/2A. Therefore the local Kummer
image W has dimension two. This uses the usual injective Kummer map;
it does not assume the reduction at 3 is good.

If the separate global descent argument supplies dim(V)<=5 and places
the global Kummer image inside V, localization rho has rank at least
four by the witnesses above. Hence dim ker(rho)<=1, and

dim rho^(-1)(W)
 = dim ker(rho) + dim(image(rho) intersect W)
 <= 1+2 = 3.

Thus this certificate closes the extra local condition required by the
(1,5) rank-upper-bound route. The global V dimension bound, the global
Kummer injection/support statement, and the other three curves remain
separate arguments; none is silently assumed to have been proved by
this script. This arithmetic and its p-adic interpretation are outside Lean.

## Reproduction

From this directory:

```sh
python3 verify_all.py
```

The two implementations use only the Python standard library and reject
optimized execution with disabled assertions. The wrapper reproduces both
outputs in a temporary directory and compares every field with the published
JSON, without overwriting inputs. It actually passed. The independent checker
uses Sylvester determinants for norms, reconstructs monic integer characteristic
polynomials for all four witnesses, verifies Hensel residue conditions directly,
and checks an odd 4-by-4 minor. It imports no code from the generator.

Final candidate certificate SHA256:
`61632519fdae0c08d6eff76c6ff227bc96a42cd8e1a92dc982d933d6c5db2352`.
The candidate certificate records the generator's SHA256. The separate
independent result is in `independent_local3.json`. This closes the local
rank-four calculation; the global dimension and Kummer-support arguments
are explained in the parent descent proof.
