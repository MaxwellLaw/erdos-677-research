# A spanning two-factor is necessary beyond an explicit threshold

Research note by MaxwellLaw, 25 October 2026.
The author, MaxwellLaw, used AI as an assistive tool.

Written mathematics only; not a
Lean theorem, complete all-length proof, counterexample, or global priority
claim. This strengthens the Hall matching necessary condition. No finite search of
possible collisions was performed.

## Sources and scope

The underlying ownership matrix, residual factorial budget, and quadratic
edge lift are prior work of Danesh–Bianchetti, *Prime-Power Transport and a
Three-Site Reduction*, sections 4.1 and Proposition 6. The inspected PDF is
[journal PDF](https://ijmttjournal.org/public/assets/volume-72/issue-9/IJMTT-V72I9P101.pdf), SHA256
`99f3db586d45c66f87280a78466b191892a030ef4577309297acd6061aab5f3f`.
Retaining the ownership matrix first gives a large-scale Hall condition.
The argument here strengthens that necessary condition to a spanning
two-factor and reproduces all arithmetic ingredients it uses.

The strengthened statement below was derived independently here, using those
prior ingredients. It has not been subjected to an exhaustive literature
priority search. It forces additional structure, but that structure is
compatible with alternating cycles and does not close the original problem.

## Statement

Let k>=2, n>=0 and m>=n+k be integers. Assume their equal-length positive
blocks have a common LCM. Put

```
F = (k-1)!,
lambda = lcm(1,...,k),
S = 2*F^(2*k+1)*k^k,
C = (3*k+2)*F^2,
T = (F*lambda)^2 * (3*k)^(2*k-2) * C^(2*k-1).
```

Retain every maximal prime power q=p^v_p(LCM) strictly greater than k.
It has a unique owner in either block. Let H_ij be the product of retained
prime powers owned by n+i and m+j, and form the simple bipartite graph with
edge (i,j) exactly when H_ij>1.

**Claim.** If n>max(S,T), this graph has two edge-disjoint perfect matchings.
Equivalently, it has a spanning 2-regular subgraph, a union of even cycles of
length at least four.

The strict cutoff q>k agrees with the paper's quadratic lift. Retaining q>=k suffices for a one-matching argument; here the strict cutoff is used. Prime powers q=k are
now assigned to the bounded residual; this avoids any unmentioned boundary
change in invoking the lift.

## 1. Defect and vertex facts

Write P(x)=product_(h=1..k)(x+h) and D(x)=P(x)/M_k(x). The exact divisibility
D(x) | F can be proved directly. For each prime p, select an index i with
maximal v_p(x+i). For h!=i,

```
v_p(x+h) <= v_p(h-i).
```

This follows by the nonarchimedean inequality when the valuations differ;
when they coincide, the difference has at least that valuation. Hence
v_p(D(x)) is at most v_p((i-1)!(k-i)!), which is at most v_p(F).

Reduce D(m)/D(n)=b/a with positive coprime integers a,b. Then a,b divide F,
1<=a<b<=F, and

```
a*P(m) = b*P(n).
```

If these inequalities are impossible for a particular k, there is already
no collision. In the remaining argument their existence is assumed.

Let L_lo be the product of omitted maximal prime powers q<=k. Then L_lo
is a divisor of lambda. With

```
n+i = s_i product_j H_ij,
m+j = t_j product_i H_ij,
```

all cofactors are positive integers and

```
product_i s_i = D(n)*L_lo <= F*lambda,
product_j t_j = D(m)*L_lo <= F*lambda.
```

For n>=k, the product ratio yields

```
(m+1)^k <= F*(n+k)^k,
m+1 <= k*(n+k),
m+k <= 3*k*n.
```

Indeed F<=k^k, n+k<=2n, and k-1<=k*n. Only this deliberately loose bound
is used below. Improved known LCM estimates can reduce the cutoff but are
not required for the statement.

## 2. Vanishing lifted edges cannot occur at arbitrary scale

Put A_i=(-1)^(i-1)(i-1)!(k-i)! and

```
L_ij = b*A_i*(n+i) - a*A_j*(m+j).
```

The paper's elementary Taylor expansion, reproduced here, gives
H_ij^2 | L_ij. Write

```
P(z-i) = A_i*z + z^2*B_i(z),  B_i in Z[z].
```

For a retained prime power q dividing both owner terms, apply this identity
at z=n+i and its j-version at z=m+j. Reduce aP(m)=bP(n) modulo q².
This gives q² | L_ij directly, without inverting any coefficient. Distinct
prime bases multiply, giving the entire H_ij squared.
This argument does not assume that L_ij is nonzero.

Suppose L_ij=0. The signs of A_i,A_j then agree. In lowest positive terms put
u/v=b*A_i/(a*A_j). Since |A_i|,|A_j|<=F, both u,v<=F^2. With t=n+i,
we have m+j=(u/v)t. Consequently the following integral polynomial vanishes
at t:

```
Q(t) = a product_(h=1..k)(u*t+v*(h-j))
       - b*v^k product_(h=1..k)(t+h-i).
```

Its leading coefficient is a*u^k-b*v^k and is nonzero. Otherwise, because
(u,v)=(a,b)=1, one obtains b=u^k and a=v^k. But every prime exponent in
F=(k-1)! is strictly less than k:

```
v_p(F) = sum_(r>=1) floor((k-1)/p^r) < k.
```

Since a,b divide F, this forces u=v=a=b=1, contrary to b>a.

Each coefficient of Q has absolute value at most S. A sufficient bound is
the sum of the absolute coefficients: the first product contributes at most
F*(F^2*k)^k=F^(2k+1)*k^k, and the second contributes at most the same amount.
The nonzero leading coefficient is an integer, hence has absolute value at
least one. For t>1+S, the leading term has absolute value at least t^k,
whereas all remaining terms together have absolute value at most
S*(t^k-1)/(t-1)<t^k. Thus every positive root has t<=1+S.

Since t=n+i>=n+1, n>S excludes L_ij=0 for every i,j, including edges not
occupied. This is an effective elementary assertion, not an irrational-limit
heuristic. It handles all possible a,b,owner pairs simultaneously.

## 3. A square-root upper bound on every occupied packet

For n> S we have n>=k and L_ij!=0. Hence

```
H_ij^2 <= |L_ij|
        <= F^2*((n+k)+(m+k))
        <= (3*k+2)*F^2*n = C*n.
```

The first inequality follows from nonzero integer divisibility. The final
one uses n+k<=2n and the preceding bound m+k<=3kn. There is no claim that
an individual H_ij must be asymptotic to sqrt(n); only the upper bound is
proved.

## 4. Exact cut products force the two-factor inequalities

Choose arbitrary subsets A of the left vertices and B of the right vertices.
Put a0=|A|, b0=|B|, and let e(A,R\\B) be the number of occupied edges from A
to the complement of B. Cancellation of all packets inside A x B gives

```
product_(i in A)(n+i) / product_(j in B)(m+j)
 = (product_(i in A)s_i / product_(j in B)t_j)
   * (product_(i in A,j outside B)H_ij
      / product_(i outside A,j in B)H_ij).
```

All omitted factors in the denominator are positive integers. Therefore,
writing e=e(A,R\\B),

```
(n+1)^a0 <= F*lambda*(m+k)^b0 * (C*n)^(e/2).
```

Suppose the capacity-two Hall inequality fails:

```
e < 2*(a0-b0).
```

Then a0>b0, and e<=2(a0-b0)-1. Squaring the preceding inequality and using
m+k<=3kn gives

```
n^(2*(a0-b0)-e)
 <= (F*lambda)^2 * (3*k)^(2*b0) * C^e
 <= (F*lambda)^2 * (3*k)^(2*k-2) * C^(2*k-1) = T.
```

The exponent on n is a positive integer, b0<=k-1, and e<=2k-1. Because n>=1,
this implies n<=T, contradicting n>T. Thus for every pair of subsets,

```
e(A,R\\B) >= 2*(|A|-|B|).
```

To see sufficiency without a probabilistic or asymptotic step, give the arcs
source->left capacity 2, each occupied left->right edge capacity 1, and each
right->sink arc capacity 2. A cut with source side {source} union A union B
has capacity

```
2*(k-|A|) + e(A,R\\B) + 2*|B| >= 2*k.
```

The integral augmenting-path argument yields a flow of value 2k: start at
the zero flow, augment by a positive integer along a residual path whenever
one exists, and note that the total value is at most 2k. The process terminates.
At termination, the vertices reachable by residual paths give a cut whose
capacity equals the flow value; the proved cut bounds force that value to be
2k. This is the classical max-flow/min-cut argument of
[Ford–Fulkerson (1956)](https://doi.org/10.4153/CJM-1956-045-5). Every left and right vertex then has exactly two used edges,
and no edge is used twice. Its support is a union of even cycles; alternating
the edges in each cycle produces two edge-disjoint perfect matchings.

## 5. What this does not prove; precise obstacle

A single Hall matching alone was insufficient in the earlier note. The new
conclusion genuinely adds a capacity restriction: a graph may have a perfect
matching and still have no spanning two-factor. For example, an isolated
matching edge cannot occur in the new large-scale regime. Every vertex must
have degree at least two, and all vertices participate in some alternating
cycle cover. No claim is made that every occupied edge belongs to that cover.

This still leaves possible cycle covers. At the exponent level, a cycle of
length 2k with every edge of size n^(1/2) satisfies both row and column growth
requirements and the proved packet upper bound. Pairwise coprimality and
consecutive vertex differences impose additional arithmetic, but the cut
inequalities alone do not contradict them. An abstract square-root growth
pattern is not a construction of actual integer packets or a counterexample.
The paper's Proposition 15 only excludes cycles made of vanishing lifted
edges; after Section 2 all lifted edges are nonvanishing, so it does not
remove these alternating cycles.

Thus no uniform contradiction, valid equal-LCM collision, complete Lean
endpoint, or whole-problem award eligibility follows. Useful continuation
would have to control simultaneous nonvanishing lifts around an alternating
cycle, or find a different route retaining enough arithmetic of the vertex
differences.

## Related public partial region result

A newly surfaced but older submission in HuanHuanHuanFFF/lean-math-lab,
commit 37e42aca251c33c62cbc2c40f286daa0526d79ee (PR 1, merged September 2026),
has the explicit Lean theorem
`B677Analytic.adopted_regions_noncollision_of_dusart`. Its assumptions include
`DusartPrimeInterval`; its region is `(m-n<=8*k) OR (n<=369*k)`. Its stated
remaining region `n>369*k, m-n>8*k` is unbounded. That is a different partial
region argument and is not a complete solution; no local replay was performed
here. The exact source inspected for its statement is

https://github.com/HuanHuanHuanFFF/lean-math-lab/blob/37e42aca251c33c62cbc2c40f286daa0526d79ee/research/tasks/B677-Lcm/runs/20260908-formalization-92c221/lean/analytic/RegionConsumer.lean

This note uses neither that conditional theorem nor its constants. It can be
compared with it without attributing a new origin to existing bridge or
binomial estimates. No build or transitive-axiom replay of that third-party project is claimed.

## Subsequent component and cycle restrictions

The [effective continuation](UNIFORM_CYCLES.md) proves component-size resonance
and, when the product-ratio radical has degree at least four, excludes pure
cycle-cover support beyond another explicit bound. It forces at least 2k+1
occupied packets in that range. Extra branching remains unresolved. These
are separate written necessary conditions, not Lean or all-length endpoints.
