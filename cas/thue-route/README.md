# A checked obstruction to a direct cubic-Thue substitution

Status: exploratory algebra, checked exactly on 2026-10-24. This is neither a solution of k=6 nor an integral-point completeness certificate. It does not rule out arithmetic reductions to finitely many Thue equations, higher-degree Thue equations, number-field unit methods, or a method using the additional square conditions.

## What was checked

Write Phi(T)=(T-1)(T-9)(T-25), and fix one of (a,b)=(1,2),(1,5),(1,10),(2,5). The relevant plane cubic is a Phi(V)=b Phi(U). Its original constraints include U=X^2, V=Y^2, X=2n+7, Y=2m+7, n>=0, m>=n+6 and the exact carry equation.

Project from the rational point (U,V)=(1,1). Put x=U-1 and t=(V-1)/(U-1). For the region of interest, x>=48, so this division is valid. Set

- A=a t^3-b;
- G=a t^2-b;
- Q(t)=a^2 t^4+3ab t^3-8ab t^2+3ab t+b^2.

The equation after removing x is

    A x^2 - 32 G x + 192(a t-b) = 0.

Its discriminant is 256 Q(t). Thus the forward map

    w=(A x-16 G)/8

satisfies w^2=Q(t), and the inverse is

    U=1+8(w+2G)/A,
    V=1+8t(w+2G)/A.

For each of the four pairs, a t^3-b is irreducible over Q, so A cannot vanish for rational t. The map is birational, with the usual finitely many projection exceptions. In particular, the forward map is defined for every point in the required region. The inverse may return x=0: this is an excluded base-point case, not a solution in that region. The exceptional original points with U=1 are V in {1,9,25}; all are outside U>=49.

The classical quartic invariants are

    I = 49 a^2 b^2,
    J = -a^2 b^2 [243(a^2+b^2)+200ab],
    4 I^3-J^2 = -243 a^4 b^4(a-b)^2(243a^2+886ab+243b^2).

They give the Jacobian y^2=x^3-27Ix-27J and

    j = 6912 I^3/(4 I^3-J^2).

The invariant formulas and Jacobian identification are standard; see [Fisher, *On binary quartics and the Cassels–Tate pairing*, section 2](https://arxiv.org/abs/2208.14977). Our substitution and arithmetic are independently checked by the script, rather than taken from a CAS transformation command.

| (a,b) | j |
| --- | --- |
| (1,2) | -120472576/26883 |
| (1,5) | -11764900/24183 |
| (1,10) | -3011814400/24350787 |
| (2,5) | -3011814400/1288467 |

All four discriminants are nonzero, and all four j-invariants are nonzero. A nonsingular binary cubic Thue curve F(p,q)=c (c nonzero), homogenized as F(p,q)=c z^3, has j=0: over the algebraic closure a change of the two coordinates sends its three distinct roots to those of p^3+q^3, producing a Fermat cubic. Since j is birationally invariant for smooth projective genus-one curves, none of these four curves is birational to such a cubic Thue curve. This is the precise, limited obstruction established here. It does not rule out finite arithmetic case splits or maps involving additional variables and square constraints.

## Why this quartic does not supply an integral-point certificate

The new t is rational, with denominator dividing U-1; it need not be integral. The inverse also has the variable denominator a t^3-b. Consequently listing the quartic's integer t,w is insufficient to exhaust original integer U,V. No finite prime-support set for these denominators has been proved.

The centered-gcd bound and carry information alone do not repair this. For example, n=120,m=126 gives X=247,Y=259, gcd(X,Y)=1 and carry(m)=2 carry(n), but t=2795/2542. These integers do NOT satisfy the curve equation; the example only shows that those additional restrictions, considered on their own, do not imply integral t or denominators supported on {2,3,5}. More generally n=60j,m=n+6 gives X=120j+7,Y=X+12 and gcd(X,Y)=1 with this same carry ratio. The gcd of X^2-1 and (X+12)^2-1 divides 20160. For any prime ell not dividing 120*20160, choose j with X=1 modulo ell. Then ell occurs in the reduced denominator of t. Thus no fixed prime-support set follows from the centered-gcd, disjointness and carry conditions alone.

Magma's [documented IntegralQuarticPoints and SIntegralQuarticPoints routines](https://magma.maths.usyd.edu.au/magma/handbook/text/1567) apply to integer quartic coordinates or a specified finite prime set. We have not established those hypotheses for this projection. They also use elliptic logarithms internally, so this projection does not itself bypass the computational issue being investigated.

There is a simpler depressed-cubic identity. With u=(3X^2-35)/4, v=(3Y^2-35)/4 and H(z)=z^3-84z-160,

    27 Phi(X^2)=64H(u),
    a v^3-b u^3 = 84(a v-b u)+160(a-b).

The right side is variable and unbounded by any estimate established here. Treating it as a fixed Thue right side is invalid. Fixing one of the finitely many possible values of gcd(X,Y) does not remove this term.

## Reproduction and remaining work

After installing the pinned packages in `cas/requirements-cas.txt`, run from the repository root:

```sh
python3 cas/thue-route/check_transforms.py
```

Actual execution succeeded with Python 3.14.6 and SymPy 1.14.0; see output.json for recorded versions and exact output. The script checks the projection identities, inverse identity, quartic invariants, discriminant factorization, j fractions, irreducibility of all four inverse denominators, and the stated finite examples. It performs exact rational/polynomial arithmetic; it does not calculate Mordell-Weil groups, certify a rank, or claim to enumerate integral points. No GRH or numerical approximation is used in these identity checks.

Still missing is either a complete algorithm with a proved treatment of the variable denominators, a different finite arithmetic descent with certified completeness, an effective global bound, or a contradiction/counterexample satisfying the original square and carry constraints. This investigation does not close that gap. The formulas above are recorded as an independently checked research route, with no assertion of priority or a new structural theorem.
