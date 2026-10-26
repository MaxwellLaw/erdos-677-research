# A quantitative lower bound on packets outside every cycle cover

Author: MaxwellLaw. Written checkpoint, 26 October 2026.
The author, MaxwellLaw, used AI as an assistive tool.

This strengthens the pure-cycle exclusion into a
necessary size condition on extra packets. It does not eliminate unbounded
branching, and no full original-problem or Lean conclusion is claimed.

Assume the same genuine collision and n>max(S,T) as in the published two-factor
result. Let B be ANY spanning two-factor contained in the occupied q>k
ownership graph E, so |B|=2k. Define the positive integer

```
W = product_(e in E outside B) H_e.
```

Let d=[Q(beta):Q], beta=(b/a)^(1/k), and use exactly Ncycle,H0,Zmax,F,D0 from
[UNIFORM_CYCLES.md](UNIFORM_CYCLES.md). The degree-two/degree-three exception-removal proof
in [UNIFORM_LOW_DEGREE.md](UNIFORM_LOW_DEGREE.md) is also required here: it implies that for every such B,

```
Q_B(beta) is irrational,
Q_B(X)=R^2 product_((i,j) in B)(b*A_i-a*A_j*X),
R=product_i s_i<=D0.
```

For d>=4 this follows from the existing conjugate-circle lemma; the cubic
exceptions are handled by the degree-two graph forcing and finite-field
argument, which apply to B regardless of any extra edges in E. Degree one or
two cannot occur under the exact normalized coefficient support.

**Claim.** The actual packets satisfy

```
n <= Ncycle * W^(2*d) <= Ncycle * W^(2*k).
```

Equivalently, for every cycle cover, its omitted packet product is at least
(n/Ncycle)^(1/(2d)). In particular no fixed bound on W can persist as n grows
for a fixed k.

Proof. Since H_e^2 divides the nonzero lift L_e on every selected edge,

```
Z_B = product_(e in B)L_e / (product_(e in B)H_e)^2
```

is an integer. The full packet product is P(n)/R, whereas the selected product
is P(n)/(R*W). Thus, with z=Z_B/W^2,

```
z = R^2*product_(e in B)L_e/P(n)^2.
```

The existing pointwise estimates use only 2k factors, the same R bound and
the same product P(n). They therefore give

```
|z| <= Zmax,
|z-Q_B(beta)| <= H0/n,
|Q_B(beta_j)| <= Zmax
```

for every conjugate beta_j. Equivalently |Z_B|<=Zmax*W^2, and
|W^2*Q_B(beta_j)-Z_B|<=2*Zmax*W^2 for each conjugate. No estimate
on W has been assumed in obtaining these bounds.

Write beta^d=B0/A0 with positive coprime A0,B0 and A0<=F. Since A0*beta is an
algebraic integer and Q_B has integer coefficients and degree 2k,

```
A0^(2k)*W^2*(Q_B(beta)-z)
```

is an algebraic integer: W^2*z=Z_B is an integer. Its norm is a nonzero
integer because Q_B(beta) is irrational and z is rational. As the other d-1
conjugate differences have absolute value at most 2Zmax, this yields

```
|Q_B(beta)-z|
 >= A0^(-2kd)*W^(-2d)*(2Zmax)^(-(d-1))
 >= F^(-2k^2)*W^(-2d)*(2Zmax)^(-(k-1)).
```

Combining with H0/n, and multiplying positive quantities, gives

```
n <= H0*F^(2k^2)*(2Zmax)^(k-1)*W^(2d)
   = Ncycle*W^(2d).
```

Finally W>=1 and d<=k give the coarser second inequality. This proves the
claim. The case W=1 recovers the earlier pure-cycle threshold.

The growth of an integer quotient by itself had prevented direct extension
of the bounded-value argument. Normalizing by W^2 converts that growth into
a rational denominator, whose exact contribution can still be bounded by
the field norm. This does not force W to be bounded, so it is a lower bound
on branching mass rather than a contradiction. No collision enumeration,
CAS output, or unproved group-height assertion is involved.

The proof and exact exponent of W were reconstructed in separate internal review. It is written mathematics, not a Lean theorem or external referee approval. The ownership packets and quadratic lifts retain the attribution in the linked source notes.
