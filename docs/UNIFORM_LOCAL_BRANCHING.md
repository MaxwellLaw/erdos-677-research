# Local branching is necessary at every ownership vertex

Author: MaxwellLaw. Written research note, 26 October 2026, evening.
The author, MaxwellLaw, used AI as an assistive tool.

This is a uniform necessary condition for a hypothetical collision, not a
complete original-problem proof, counterexample, Lean endpoint, or global
priority claim.

## New statement

Use the canonical q>k prime-power ownership packets from the published
[UNIFORM_STRUCTURE.md](UNIFORM_STRUCTURE.md). Suppose k>=2, n>=0, m>=n+k and
M_k(n)=M_k(m). Let E be the occupied bipartite graph. Put

```
F = (k-1)!,
lambda = lcm(1,...,k),
D0 = F*lambda,
S = 2*F^(2*k+1)*k^k,
C = (3*k+2)*F^2,
J = 4*k^2*(1+(3*k)^(k-1)),
Zlocal = D0^2*C^2,
Hlocal = 2*D0^2*C*F^2*J,
Nvertex = Hlocal*F^(2*k)*(2*Zlocal)^(k-1).
```

Let d=[Q(beta):Q], beta=(b/a)^(1/k), where aP_k(m)=bP_k(n) is the reduced
product-ratio equation. The exact normalized coefficient support proves
3<=d<=k; its proof is recalled below.

**Local packet theorem.** Assume n>S. At any left or right vertex with at
least two occupied edges, choose ANY TWO of them. If V is the product of
all its other incident packets, then

```
n <= Nvertex*V^(2*d) <= Nvertex*V^(2*k).                  (L)
```

**Minimum-degree consequence.** If

```
n > max(S, D0^2*C, Nvertex),
```

then every vertex has degree at least three. Hence **|E|>=3k**.

For a vertex of degree exactly three, (L) applies to each individual packet
H by selecting the other two edges; thus n<=Nvertex*H^(2d) for every incident
packet. More generally, the product remaining after deletion of ANY two
incident edges must grow at least as (n/Nvertex)^(1/(2d)). Bounded small extra
packets at an otherwise two-edge vertex cannot satisfy the large-scale
conditions.

This differs from the previous whole-cycle-cover bound: branching is now
required locally at every vertex. No global perfect matching or spanning
cycle-cover hypothesis is needed for this theorem.

## 1. Prior arithmetic ingredients and exact degree range

Write

```
A_i=(-1)^(i-1)*(i-1)!*(k-i)!,
L_ij=b*A_i*(n+i)-a*A_j*(m+j).
```

The ownership factorization and quadratic lift, due to [Danesh–Bianchetti](https://ijmttjournal.org/public/assets/volume-72/issue-9/IJMTT-V72I9P101.pdf),
section 4.1 and Proposition 6, give

```
n+i = s_i*product_j H_ij,
m+j = t_j*product_i H_ij,
H_ij^2 | L_ij,
product_i s_i <= D0,
product_j t_j <= D0.
```

All residuals are positive integers; in particular s_i,t_j<=D0. The earlier
independent Cauchy-root argument in [UNIFORM_STRUCTURE.md](UNIFORM_STRUCTURE.md) proves that n>S
implies L_ij!=0 for every i,j. It also proves n>=k, m+k<=3kn, and

```
H_ij^2 <= C*n                                           (P)
```

on every occupied edge. These ingredients are not claimed as new here.

The exact normalization, rechecked in [UNIFORM_LOW_DEGREE.md](UNIFORM_LOW_DEGREE.md) from
Danesh–Bianchetti Lemma 1, says

```
a*b | Q_k=lcm(1,...,k)/k,   gcd(a,b)=1,   1<=a<b.
```

The field-norm proof gives

```
d=k/g,
g=gcd(k,{v_p(b)-v_p(a):p divides a*b}).
```

Degree one is impossible because v_p(Q_k)<k. If d=2, k=2r and some prime
satisfies p^r|Q_k, hence 2^r<=2r. Induction from 2^3>2*3 excludes r>=3.
The two remaining values k=2,4 have Q_k=1,3 and admit no nonzero prime
valuation divisible by k/2. Thus d>=3 in every hypothetical collision.
The earlier classification of d=3 and its modular certificates are not
needed for this new local theorem.

As in the existing norm argument, write beta^d=B0/A0 in lowest positive
terms, with A0,B0<=F. Then A0*beta is an algebraic integer. For theta=1/beta,
B0*theta is an algebraic integer, and theta has the same exact degree d.
The coefficient bounds a,b<=F and |A_i|<=F hold throughout.

## 2. A uniform ratio approximation

Put rho=m/n. The known bound m+k<=3kn gives 1<rho<=3k, and
1<beta<=F^(1/k)<=k. For h=1,...,k,

```
|(m+h)/(n+h)-rho| <= 4*k^2/n.
```

Both factors are at most 3k. Telescoping the product of all k factors gives

```
|rho^k-beta^k| <= 4*k^3*(3*k)^(k-1)/n.
```

Since rho,beta>=1, factoring their kth powers gives

```
|rho-beta| <= D/n,
D=4*k^2*(3*k)^(k-1).
```

For arbitrary i,j the left-normalized ratios therefore satisfy

```
|(m+j)/(n+i)-beta| <= (4*k^2+D)/n = J/n.                 (A)
```

Indeed their difference from rho is (j-rho*i)/(n+i), bounded by 4k^2/n.
For the right-normalized ratios, first compare with 1/rho:

```
|(n+i)/(m+j)-1/rho|
 = |m*i-n*j|/(m*(m+j)) <= 2*k/n.
```

Also |1/rho-1/beta|<=|rho-beta| because rho,beta>=1. Since 2k<=4k^2,

```
|(n+i)/(m+j)-theta| <= J/n,    theta=1/beta.              (A')
```

All denominators are positive; n>S>=k ensures no division by zero.

## 3. The left-vertex integer and a quadratic irrational value

Fix a left vertex i and two distinct occupied neighbors j1,j2. Let V be the
product of the other packets at i, and let s=s_i. The positive integer owner
factorization is

```
n+i = s*V*H_(i,j1)*H_(i,j2).
```

Since each selected packet square divides its own lift, the quantity

```
Z = L_(i,j1)*L_(i,j2)/(H_(i,j1)*H_(i,j2))^2
```

is an integer. It can have either sign. Divide it by V^2 and set z=Z/V^2.
The exact identity is

```
z = s^2*product_(j in {j1,j2})(b*A_i-a*A_j*(m+j)/(n+i)).
```

Define the integer-coefficient polynomial

```
Q(X)=s^2*(b*A_i-a*A_j1*X)*(b*A_i-a*A_j2*X).
```

It has degree exactly two: its leading coefficient
s^2*a^2*A_j1*A_j2 is nonzero. Since beta has degree d>=3, Q(beta) is
irrational. Otherwise Q(X)-Q(beta) would be a nonzero rational polynomial
of degree two annihilating beta. This simple degree argument replaces the
whole-cycle conjugate-circle argument in the local setting.

Each actual factor and each comparison factor at beta has absolute value
at most C. By (A), their difference is at most F^2*J/n. Telescoping just
these two factors proves

```
|z-Q(beta)| <= Hlocal/n,
|z| <= Zlocal.                                          (B)
```

Every conjugate beta_j has modulus beta<=k, so its two polynomial factors
also have absolute value at most C. Hence

```
|Q(beta_j)| <= Zlocal                                   (C)
```

for all conjugates. The scale bounds s<=D0 were included in Hlocal and Zlocal.

Now A0^2*V^2*(Q(beta)-z) is an algebraic integer: Q has integer coefficients
and degree two, A0*beta is integral, and V^2*z=Z is an integer. Its norm is a
nonzero integer since Q(beta) is irrational while z is rational. Bounding
all d-1 other conjugate differences by 2Zlocal via (B),(C) yields

```
|Q(beta)-z|
 >= A0^(-2*d)*V^(-2*d)*(2*Zlocal)^(-(d-1))
 >= F^(-2*k)*V^(-2*d)*(2*Zlocal)^(-(k-1)).                (D)
```

Combine (B) and (D), multiply positive quantities, and obtain
n<=Hlocal*F^(2k)*(2Zlocal)^(k-1)*V^(2d)=Nvertex*V^(2d).
Since V>=1 and d<=k, the second inequality in (L) also follows.

## 4. Right vertices, without a hidden symmetry assumption

Fix a right vertex j with two distinct incident left vertices i1,i2. Put
t=t_j and let V be the product of the other packets in that column. Then

```
m+j=t*V*H_(i1,j)*H_(i2,j),
Z=L_(i1,j)*L_(i2,j)/(H_(i1,j)*H_(i2,j))^2 is an integer,
z=Z/V^2=t^2*product_(i in {i1,i2})(b*A_i*(n+i)/(m+j)-a*A_j).
```

Use the polynomial

```
Q(X)=t^2*(b*A_i1*X-a*A_j)*(b*A_i2*X-a*A_j)
```

at theta=1/beta. It again has degree exactly two, with nonzero leading
coefficient t^2*b^2*A_i1*A_i2. Hence Q(theta) is irrational. The actual
ratios (n+i)/(m+j) are between zero and one by disjointness, as is theta;
all actual and conjugate polynomial factors have modulus at most 2F^2<=C.
Estimate (A') supplies the same F^2*J/n approximation. Thus (B),(C) hold
with theta and the same Hlocal,Zlocal.

Finally B0*theta is integral with B0<=F. Replacing A0 by B0 in the norm
argument gives the same lower bound (D) and exactly the same conclusion (L).
The proof does not interchange n and m or assume their order can be reversed.

## 5. Minimum degree and the explicit edge lower bound

If a vertex has degree zero, its owner number equals its residual, at most
D0. Since every owner number is at least n+1, this is impossible when
n>D0^2*C>=D0.

If a vertex has degree one, write its owner as u=r*H with r<=D0. Every owner
is at least n+1, and (P) gives

```
(n+1)^2 <= r^2*H^2 <= D0^2*C*n.
```

For n>0 this implies n<=D0^2*C. Thus degrees zero and one are excluded by
the stated threshold without any matching theorem.

If a vertex has degree exactly two, V=1 in (L), so n<=Nvertex. It too is
excluded beyond the displayed maximum. Every vertex therefore has degree at
least three; summing degrees over the k left vertices gives |E|>=3k.

At a degree-three vertex, choosing any two edges leaves precisely the third
packet H as V, proving n<=Nvertex*H^(2d) for each of its three packets.

## Scope and remaining obstruction

This proves a strictly stronger uniform structural necessity than excluding
a pure cycle cover. It also excludes large configurations consisting of a
nearly two-edge vertex with only bounded extra packets. The argument applies
to each row and column individually, with exact integer divisibility and an
effective norm bound.

It does not force V to be bounded, does not exclude graphs of minimum degree
at least three, and does not supply a valid interval collision. For example,
row/column exponent sums equal to one can distribute positive mass among
three or more edges while respecting the earlier 1/2 edge upper bound.
Those growth patterns are not constructed integer collisions, but demonstrate
why these inequalities alone are not a contradiction.

The retained ownership/factorial/lift ingredients are prior mathematics. The
local quadratic-product argument and its explicit degree-three consequence
were derived here; no exhaustive priority search or worldwide originality
claim is made. The proof uses ordinary algebraic degree/norm and rational
inequalities, no CAS output and no finite collision enumeration. It is not
Lean-formalized in this note and creates no whole-problem award eligibility.

The exact inequalities, both vertex orientations, algebraic norm exponents and degree-zero/one boundary cases were reconstructed in separate internal review. This is not external referee approval. The inspected primary-paper SHA256 remains `99f3db586d45c66f87280a78466b191892a030ef4577309297acd6061aab5f3f`; no corresponding local two-edge quotient statement was found in that inspected source, which is not an exhaustive priority determination.
