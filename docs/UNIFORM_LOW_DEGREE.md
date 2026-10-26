# Removing the small-radical-degree exception from the cycle restriction

Author: MaxwellLaw. Written research checkpoint, 26 October 2026.
The author, MaxwellLaw, used AI as an assistive tool.

No complete all-length solution, Lean endpoint, or global priority claim is
made here. This note advances the previously unresolved degree-two/degree-
three part of the pure-cycle-support argument. It does not repeat a search
for interval collisions.

## Result and dependencies

Use S,T,Ncycle and the retained q>k ownership graph defined in the published
[UNIFORM_STRUCTURE.md](UNIFORM_STRUCTURE.md) and [UNIFORM_CYCLES.md](UNIFORM_CYCLES.md).

**Theorem.** For every k>=2, if a genuine equal-LCM collision satisfies
n>max(S,T,Ncycle), its ownership graph has at least 2k+1 occupied packets.
The previously imposed radical-degree-at-least-four hypothesis is unnecessary.

The two-factor, nonzero lift, pointwise approximation, and norm-separation
proofs are unchanged. The work here classifies all smaller radical degrees
using the exact prior defect normalization, then proves the required
irrationality for its two cubic exceptions with five small-prime witnesses.
Graphs with more than 2k edges still remain; the original all-k question is
not resolved.

The exact defect normalization is prior work of Danesh–Bianchetti, *Prime-
Power Transport and a Three-Site Reduction*
([primary paper](https://ijmttjournal.org/public/assets/volume-72/issue-9/IJMTT-V72I9P101.pdf)), section 2, Lemma 1 and equations
(6)-(14), building on the product/LCM literature. The inspected primary PDF
has SHA256 99f3db586d45c66f87280a78466b191892a030ef4577309297acd6061aab5f3f.
Its proof is reconstructed below to check every n>=0 boundary. The inspected
paper does not state this radical-degree classification or the finite-field
product obstruction; this is a source-local comparison only.

## 1. Exact normalized coefficient support

Put P_k(x)=product_(i=1..k)(x+i), M_k(x)=lcm(x+1,...,x+k),
D_k(x)=P_k(x)/M_k(x), lambda_k=lcm(1,...,k), and

```
B_k = k!/lambda_k,
Q_k = lambda_k/k.
```

These are integers. For a prime p, set A=floor(log_p k), the largest exponent
with p^A<=k. Let N_r(x) count multiples of p^r in the k-term block. Counting
prime valuations level by level gives

```
v_p(D_k(x)) = sum_(r=1..A)(N_r(x)-1).
```

Indeed for r<=A every length-k block contains at least one multiple of p^r;
for r>A it contains at most one, so the contribution to sum minus maximum
is zero. In particular N_r(x)>=floor(k/p^r), and therefore

```
v_p(D_k(x)) >= sum_(r=1..A)(floor(k/p^r)-1)
             = v_p(k!)-A = v_p(B_k).
```

The upper divisibility D_k(x)|(k-1)! follows by selecting an owner of the
maximal p-valuation: each other valuation is at most that of its nonzero
index difference, whose total is bounded by v_p((k-1)!). Thus

```
B_k | D_k(x) | (k-1)!,
E_k(x)=D_k(x)/B_k divides Q_k.
```

No step requires x>0; the positive block starting at x=0 is included.
If n<m and M_k(n)=M_k(m), reduce D_k(m)/D_k(n)=b/a. Then a,b are positive
coprime, a<b, and a,b individually divide Q_k. Their coprimality yields

```
a*b | Q_k,
a*P_k(m)=b*P_k(n).
```

This is stronger than only a,b | (k-1)!, already used in the public structural
proof. Since k divides lambda_k, all definitions include small k correctly.

## 2. Complete classification of degrees at most three

Let beta=(b/a)^(1/k)>1. The published field-norm argument gives its exact
radical degree

```
d = k/g,
g = gcd(k,{v_p(b)-v_p(a): p divides a*b}).
```

Degree one is impossible: it would make every nonzero valuation of a*b a
positive multiple of k, whereas
v_p(Q_k)=floor(log_p k)-v_p(k)<k for k>=2.

Suppose d=s with s in {2,3}. Then k=s*r and g=r. At least one valuation of
a*b is a nonzero multiple of r. Since a*b|Q_k, for some prime p,

```
p^r <= Q_k's p-primary part <= k,
2^r <= s*r.                                             (1)
```

For s=2 and r>=3, the opposite inequality 2^r>2r follows by induction from
8>6 (doubling exceeds the next linear term). Hence k can only be 2 or 4.
But Q_2=1 and Q_4=3; neither has a nonzero prime valuation divisible by k/2.
**Degree two never occurs.**

For s=3 and r>=4, 2^r>3r similarly follows by induction from 16>12. Thus k
can only be 3,6 or 9. Now

```
Q_3=2,
Q_6=10,
Q_9=280=2^3*5*7.
```

For k=6 all nonzero valuations would have to be multiples of two, impossible
in Q_6. For k=3, a*b|2 and b>a force (a,b)=(1,2). For k=9 all nonzero
valuations must be multiples of three; only 2^3 in Q_9 is available, forcing
(a,b)=(1,8). Both yield beta=cuberoot(2).

Consequently the entire list of degree-three possibilities is

```
(k,a,b)=(3,1,2) or (9,1,8).
```

This is a uniform proof with a few terminal integer identities, not a scan
through finitely many k or through interval starts.

## 3. An elementary modular obstruction to rational products

Let alpha=cuberoot(2), and let

```
G(X) = product_e(c_e-d_e*X) in Z[X].
```

Suppose a prime p satisfies:

1. p is different from 2 and 3, and p=2 mod 3;
2. every d_e is nonzero modulo p;
3. for at least one edge e, p divides c_e^3-2*d_e^3.

Then **G(alpha) is irrational**.

Proof. The minimal polynomial X^3-2 is irreducible over Q by Eisenstein at 2.
If G(alpha) were rational, division by this monic polynomial in Z[X] would
have a constant integer remainder z; independence of 1,alpha,alpha^2 forces
the other two remainder coefficients to vanish. Reduce the identity
G(X)=H(X)(X^3-2)+z modulo p.

Because gcd(3,p-1)=1, cubing permutes the nonzero elements of F_p. Thus
X^3-2 has exactly one root r in F_p. It is simple since 3r^2 is nonzero.
The remaining quadratic factor X^2+rX+r^2 is irreducible: a root would give
a second cubic root, or the already excluded repeated root. Assumption 3
and d_e!=0 give c_e/d_e=r, so G(r)=0 and therefore z=0 modulo p. It follows
that the irreducible quadratic divides G modulo p. But every factor of G is
a nonconstant linear polynomial modulo p, contradicting unique factorization
in F_p[X]. This proves the lemma.

Multiplying G by any nonzero rational scalar does not change rationality.
In particular the bounded residual factor R^2 in the cycle polynomial, or a
common integer factor in all endpoint weights, must be cancelled first; no
assumption that p avoids R is needed.

## 4. The two cubic cases

Suppose exactly 2k packets are occupied and n>max(S,T). The published
spanning two-factor theorem implies that every vertex of the entire support
has degree exactly two: a spanning two-factor already uses all 2k edges.
The polynomial from the integer product of lifts is

```
Q(X)=R^2 product_((i,j) in E)(b*A_i-a*A_j*X),
A_i=(-1)^(i-1)(i-1)!(k-i)!.
```

### k=3, (a,b)=(1,2)

The endpoint weights are [2,-1,2]. The right vertex of weight -1 has two
distinct incoming neighbors, whereas only one left vertex has weight -1.
Thus some occupied edge goes from weight 2 to weight -1. Its factor is
4+X, and its norm at alpha is 4^3-2*(-1)^3=66=6*11.
Take p=11. All endpoint weights are nonzero modulo 11, and 11=2 mod 3.
Section 3 proves that the product of all edge factors at alpha is irrational.
Therefore Q(alpha) is irrational as well.

### k=9, (a,b)=(1,8)

The endpoint weights are 144 times

```
w=[280,-35,10,-5,4,-5,10,-35,280].
```

After cancelling the nonzero rational factor R^2*144^18, the polynomial is
product_(i,j in E)(8*w_i-w_j*X). Every endpoint weight has prime support
contained in {2,5,7}.

A left vertex of weight 10 has two distinct neighbors, while exactly one
right vertex has weight 4. Thus an occupied edge from this left vertex must
have terminal weight among 280,-35,10,-5. The following exact witnesses apply:

| terminal weight v | (8*10)^3-2*v^3 | witness prime p | quotient norm/p |
|---:|---:|---:|---:|
| 280 | -43,392,000 | 113 | -384,000 |
| -35 | 597,750 | 797 | 750 |
| 10 | 510,000 | 17 | 30,000 |
| -5 | 512,250 | 683 | 750 |

Each witness is prime and congruent to two modulo three. None divides any
endpoint weight. Whichever terminal weight occurs, Section 3 shows that
the entire product is irrational. Hence Q(alpha) is irrational.

The graph argument uses only the degree-two property and the displayed
multiplicities, and does not enumerate graphs or assume a particular cycle
shape. In particular it handles any union of alternating cycles.

## 5. Substitution into the existing effective bound

All possible degree-two cases were excluded; the only degree-three cases
now satisfy the same irrationality conclusion as the degree-at-least-four
concavity argument. Thus Q(beta) is irrational in every possible collision
with exactly 2k packets and n>max(S,T).

The existing norm separation proof used only that irrationality, beta's exact
degree d<=k, and the displayed coefficient bounds. It remains valid for d=3:

```
|Q(beta)-Z| >= F^(-2*k^2)*(2*Zmax)^(-(k-1)),
|Q(beta)-Z| <= H0/n.
```

The same Ncycle=H0*F^(2*k^2)*(2*Zmax)^(k-1) therefore contradicts n>Ncycle.
The spanning two-factor gives at least 2k edges, and equality is excluded,
proving at least 2k+1 with no radical-degree hypothesis.

## Verification and limits

`cas/uniform/cubic_obstruction_certificate.py` uses Python's standard library. It checks
all five witness primes by trial division, every displayed norm divisibility,
the actual signed factorial weights, all possible edge-factor degrees modulo
the chosen prime, the unique cubic root and absence of roots of its quadratic
cofactor. These checks run over only 1,621 finite-field residue classes in each
of two complementary root tests; they are not a search for LCM collisions.
The graph forcing is proved above; the script checks its exact multiplicities.
Its output must agree exactly with the saved JSON witnesses. Keep assertions enabled.

Discovery used SymPy 1.14.0 only to factor the 25 possible normalized k=9
edge norms. The completed proof uses just four displayed factors and the
k=3 witness, independently checked without SymPy. No full factorization is
needed, and no CAS completeness assertion is a premise.

This new conclusion is a written mathematical structural theorem. The cubic
polynomial/finite-field argument and the analytic cycle framework are not
claimed to be Lean-formalized here. Additional edges remain the actual global
obstacle: for edge count e>2k, the integer product-of-lifts quotient has scale
n^(e-2k), and the bounded-integer separation argument does not eliminate it.
No whole-problem award eligibility follows.

Reproduce from the repository root:

```sh
python3 cas/uniform/cubic_obstruction_certificate.py
python3 cas/uniform/verify_cubic_discriminants.py
```

The second checker independently tests the quadratic discriminants by Euler's criterion, without importing the first checker or enumerating roots. Separate internal review reconstructed the normalization, graph forcing and norm-bound substitution. This is not external referee approval.

The [quantitative continuation](UNIFORM_BRANCHING.md) proves that for every selected spanning cycle cover, the omitted packet product W satisfies n<=Ncycle*W^(2d). It restricts the size of branching without excluding unbounded W.
