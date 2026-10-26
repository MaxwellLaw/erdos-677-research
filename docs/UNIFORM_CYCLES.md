# Effective component and cycle restrictions for all lengths

Author: MaxwellLaw. Written mathematical checkpoint, 25 October 2026.
The author, MaxwellLaw, used AI as an assistive tool.

The [26 October continuation](UNIFORM_LOW_DEGREE.md) removes the d>=4
restriction below. The earlier proof and its exact original scope are
preserved here; the remaining obstruction is additional branching.

**Scope of this 25 October argument.** Under explicit large-start bounds, component sizes satisfy a
radical-degree divisibility condition. If that degree is at least four, a
genuine collision must have at least `2k+1` occupied prime-power packets;
its support cannot consist solely of an alternating cycle cover. Graphs
with additional branching remain unresolved. This is written mathematics,
not a Lean theorem, full original-problem solution or counterexample.

Use the constants F,lambda,S,T and the retained q>k graph from the
[spanning two-factor theorem](UNIFORM_STRUCTURE.md). The ownership packets,
factorial residual budgets and quadratic lifts are prior work of
[Danesh–Bianchetti](https://ijmttjournal.org/public/assets/volume-72/issue-9/IJMTT-V72I9P101.pdf),
section 4.1 and Proposition 6. Their Proposition 15 excludes cycles of
vanishing lifts. The argument below instead treats a product of nonzero
lifts and gives an effective exclusion of pure cycle support.

The inspected PDF has SHA256
`99f3db586d45c66f87280a78466b191892a030ef4577309297acd6061aab5f3f`.
The component and product-of-lifts arguments below were not found in that
inspected paper; this is a source-local comparison, not an exhaustive
literature priority determination. All estimates and completeness of the
finite graph arguments are proved below without a collision search or CAS.

## 1. A real-rooted polynomial cannot take a rational value here

Let beta>0 have minimal polynomial X^d-r over Q, with r>0 rational and d>=4.
Let P be a nonconstant rational polynomial all of whose roots are nonzero rational numbers. Then P(beta) is not rational.

Suppose instead P(beta)=z in Q. Let zeta=exp(2*pi*i/d). All beta*zeta^j are
conjugates, so P(beta*zeta^j)=z for every j. The value z is nonzero, since a
zero value would make nonreal conjugates roots of the real-rooted P.

Write P(X)=c product_s(X-r_s), with real nonzero r_s. For t in [-1,1] put

```
F(t) = sum_s log(beta^2+r_s^2-2*beta*r_s*t).
```

Each logarithm has a strictly positive argument throughout [-1,1]. A zero
could only occur at t=+/-1 and r_s=+/-beta; irrationality of beta and
rationality of r_s exclude that possibility.

The second derivative is

```
F''(t) = -sum_s (2*beta*r_s)^2 /
                 (beta^2+r_s^2-2*beta*r_s*t)^2 < 0.
```

Hence F is strictly concave. But

```
F(cos(2*pi*j/d)) = 2*log|z/c|
```

for every j, because each summand is the logarithm of the squared modulus
of beta*zeta^j-r_s. For d>=4, j=0,1,2 give three distinct cosines. The middle
one is a strict convex combination of the other two, contradicting strict
concavity. This proves the assertion. All roots in the application below are rational, as required.

This is stronger than merely observing that beta is irrational. Products of
linear forms can otherwise conceivably return rational values.

## 2. The exact radical degree

Let a,b be positive coprime integers with b>a, and beta=(b/a)^(1/k). Put

```
g = gcd(k, {v_p(b)-v_p(a): p divides a*b}),
d = k/g.
```

Then beta has degree exactly d over Q and minimal polynomial X^d-B/A,
where b=B^g and a=A^g, A,B positive coprime integers. Positivity gives
beta^d=B/A. The degree h is at most d because beta is a root of X^d-B/A. Take the field norm from Q(beta):

```
Norm(beta)^d = (B/A)^h.
```

Comparing prime valuations yields d | h*(v_p(B)-v_p(A)) for every p. The gcd
of d and these valuation differences is one by construction, so Bezout's
identity gives d|h. Since 0<h<=d, the degree is exactly d. This proof
does not need a general binomial-irreducibility theorem.

## 3. The integer supplied by exactly 2k occupied edges

Assume a genuine collision with n above the no-vanishing threshold S of the
[preceding theorem](UNIFORM_STRUCTURE.md). Retain maximal prime powers q>k. Let E be the occupied owner
pairs and suppose |E|=2k. Put

```
R = product_i s_i <= D0 = F*lambda,
L_ij = b*A_i*(n+i)-a*A_j*(m+j),
A_i = (-1)^(i-1)*(i-1)!*(k-i)!.
```

Every L_ij is nonzero and H_ij^2 divides L_ij. Since
product_E H_ij=P(n)/R, the exact quantity

```
Z = product_E L_ij / (product_E H_ij)^2
  = R^2 * product_E L_ij / P(n)^2
```

is an integer, possibly negative. Define the integer-coefficient polynomial

```
Q(X) = R^2 product_((i,j) in E)(b*A_i-a*A_j*X).
```

It has degree 2k and every root b*A_i/(a*A_j) is a nonzero rational number.
If the radical degree d>=4, Section 1 proves Q(beta) irrational. The argument
below compares the actual integer Z directly with Q(beta), using the actual
bounded residual R. No passage to an infinite sequence, or silently fixed
configuration along a changing sequence, is needed.

## 4. Uniform explicit separation and approximation bounds

Use F=(k-1)!, lambda=lcm(1,...,k), D0=F*lambda and C=(3k+2)*F^2. Define

```
B0 = F^2*(2*k+4*k^2*(3*k)^(k-1)),
Zmax = D0^2*C^(2*k),
H0 = D0^2*(2*k*C^(2*k-1)*B0 + C^(2*k)*k^2*2^(2*k)),
Ncycle = H0 * F^(2*k^2) * (2*Zmax)^(k-1).
```

All are positive integers depending only on k. We prove that exactly 2k
occupied edges is impossible when n>max(S,Ncycle) and d>=4.

First, n>=k and m+k<=3kn give |L_ij/n|<=C, hence |Z|<=Zmax. Every conjugate
beta*zeta^j has modulus beta<=k; therefore |Q(beta*zeta^j)|<=Zmax as well.

The denominator A in beta^d=B/A satisfies A<=a<=F, and A*beta is an algebraic
integer. Consequently A^(2k)*(Q(beta)-Z) is an algebraic integer. Its norm
is a nonzero integer because Q(beta) is irrational. Bounding all d-1 other
conjugate factors by 2*Zmax proves

```
|Q(beta)-Z| >= A^(-2*k*d)*(2*Zmax)^(-(d-1))
             >= F^(-2*k^2)*(2*Zmax)^(-(k-1)).                 (1)
```

For the other direction, put rho=m/n. The same product telescoping estimate
proved in Section 6 below proves

```
|rho-beta| <= 4*k^2*(3*k)^(k-1)/n.
```

Thus each factor f_ij=L_ij/n differs from its comparison factor
q_ij=b*A_i-a*A_j*beta by at most B0/n; both factors have absolute value at
most C. Product telescoping over the 2k edges gives

```
|product_E f_ij - product_E q_ij| <= 2*k*C^(2*k-1)*B0/n.
```

Also

```
D_n = P(n)^2/n^(2*k) = product_(h=1..k)(1+h/n)^2 >= 1,
|D_n-1| <= k^2*2^(2*k)/n.
```

The second inequality is product telescoping over 2k factors, all between one
and two. Since |1/D_n-1|<=|D_n-1| and
Z=R^2*product_E f_ij/D_n, this yields

```
|Z-Q(beta)| <= H0/n.                                     (2)
```

When n>Ncycle, (2) is strictly smaller than the lower bound (1), a
contradiction. This is an effective exact separation proof; no numerical
approximation to beta or its conjugates is needed to establish the bound.

## 5. Result and remaining obstruction

Combining this with the earlier spanning two-factor theorem gives:

> If d>=4 and n>max(S,T,Ncycle), every genuine collision has at least 2k+1
> occupied q>k ownership packets. Its support therefore cannot consist solely
> of an alternating cycle cover; some additional branching is required.

The d>=4 hypothesis is explicit. For the four k=6 ratios 2,5,10,5/2, d=6,
so it applies. No new k=6 solution is needed: the separate completed proof
already handles every n. This is instead a uniform structural continuation.
For small radical degree d=2 or 3 the concavity argument does not provide
three distinct cosine values, and no exclusion is asserted here.

Graphs with more than 2k occupied packets remain possible under these
necessary conditions. Their product-of-lifts quotient need not remain in a
bounded set: its scale is n^(|E|-2k). Therefore the same bounded-integer
argument cannot simply be repeated to remove arbitrary extra edges. No
uniform contradiction or valid counterexample has been obtained.

The claim has not been Lean-formalized. The use of field norms, logarithms,
strict concavity and conjugates is explicit human mathematics. No CAS result,
finite collision search or unproved custom axiom is used.

## 6. Component-size resonance and connectedness

Use k,F,lambda,S,T from [the preceding theorem](UNIFORM_STRUCTURE.md), and put

```
D0 = F*lambda,
Tc = 8*k^4*(3*k)^(2*k-2)*F^k*D0^(2*k-1).
```

Assume a genuine collision with n>max(S,T,Tc). Write the reduced original
product ratio as P(m)/P(n)=b/a, a,b positive coprime divisors of F, b>a. Define

```
g = gcd(k, {v_p(b)-v_p(a) : p divides a*b}),
ell = k/g (= d in Sections 1–5).
```

The gcd uses absolute integer valuations, so signs cause no ambiguity.
Then **every connected component of the q>k ownership graph contains r left
vertices and r right vertices with ell dividing r**. In particular, whenever
g=1, the graph must be connected. This applies to every prime k under the
hypothetical collision assumptions.

The component is balanced because the preceding theorem supplies a perfect
matching (indeed two); restricting the matching to a component gives a
bijection between its left and right vertices. Write its left and right sets
as A,B, each of size r. Cancelling all internal packets gives exactly

```
product_(j in B)(m+j) / product_(i in A)(n+i)
 = product_(j in B)t_j / product_(i in A)s_i = q.
```

The numerator and denominator of q in lowest terms are each at most D0,
because the joint residual products are at most D0. This is a bounded-height
rational q; its actual value may depend on the collision.

Put rho=m/n and beta=(b/a)^(1/k). Since n>=k, the earlier estimates give
1<rho<=3k and 1<beta<=k. Choose any pairing of the r left/right indices.
Each factor (m+j)/(n+i) differs from rho by at most

```
(k+rho*k)/n <= 4*k^2/n,
```

and both it and rho are at most 3k. The elementary product telescoping
identity therefore gives, for r<=k,

```
| product_(paired i,j) ((m+j)/(n+i)) - rho^r |
 <= E/n,  E=4*k^3*(3*k)^(k-1).
```

Applied to the full k-term ratio this also proves
|rho^k-beta^k|<=E/n. Since rho,beta>=1, factorization of the difference of
kth powers yields |rho-beta|<=E/(k*n). Hence

```
|q-beta^r| <= J/n,
J = 8*k^3*(3*k)^(2*k-2).
```

Suppose q!=beta^r. If q=u/v in lowest terms, then

```
|q^k-(b/a)^r| >= 1/(v^k*a^r) >= 1/(D0^k*F^k).
```

Also q<=D0 and beta^r<=F<=D0, so factoring the difference of kth powers gives

```
|q^k-(beta^r)^k| <= k*D0^(k-1)*|q-beta^r|.
```

Thus |q-beta^r|>=1/(k*F^k*D0^(2*k-1)), contrary to n>Tc. Consequently
q=beta^r is rational. Comparing prime valuations in q^k=(b/a)^r gives

```
k | r*(v_p(b)-v_p(a))  for every prime p,
```

which is equivalent to ell|r by Bezout's identity for the finite gcd.
Because at least one valuation is nonzero and every absolute valuation is
strictly below k (a,b divide (k-1)!), ell>=2. If k is prime, the same facts
force g=1 and ell=k. No binomial irreducibility theorem, limit passage along
an assumed infinite sequence, or unproved fixed-ratio recurrence is used.


Together with Section 5, this shows that, beyond the maximum of the displayed
thresholds, a collision with d=k>=4 would have a connected ownership graph
with at least 2k+1 edges. This applies in particular to prime k>=5. When d is
a proper divisor of k, each component still has size a positive multiple of d.

These restrictions do not remove graphs with extra occupied edges. Cancelling
packet ratios around a full cycle reproduces the original product identity;
it does not create a second independent equation. Nor does beta's
irrationality alone prove arbitrary expressions in beta irrational. The
strict-concavity argument above supplies the precise irrationality statement
needed for the bounded integer quotient when the edge count is exactly 2k.
For larger edge counts that quotient grows like n^(|E|-2k), so the same
bounded-value argument does not provide a contradiction.

## Review and formalization boundary

The exact constants, field-degree argument, norm lower bound, product
approximation and graph implications were reconstructed in separate internal checks. No external human referee approval is claimed. The
proof uses elementary real calculus, algebraic conjugates and field norms,
with every numerical constant supplied symbolically. No finite search,
probabilistic assumption, CAS assertion or Lean axiom enters this argument.
It has not been Lean-formalized and does not change the all-length or award
eligibility status recorded in [RESEARCH_STATUS.md](RESEARCH_STATUS.md).
