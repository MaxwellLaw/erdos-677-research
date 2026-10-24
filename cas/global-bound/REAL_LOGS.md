# Certified real periods and elliptic logarithms

Author: MaxwellLaw. Mathematical proof and reproducible arithmetic, 2026-10-24.

The author, MaxwellLaw, used AI as an assistive tool.

This note justifies the rational intervals in `real_logs.json` for the four elliptic models, their displayed rational generators, and the specified algebraic point Q0. The normalization is the invariant differential `dx/(2y)`. The analytic identities and this interval argument are human mathematics, not Lean theorems. These intervals supply inputs to the separate initial-bound and lattice arguments; by themselves they are not a complete integer-point calculation.

## Exact arithmetic and domains

`certify_real_logs.py` uses Python integers and `fractions.Fraction`. At precision B, its interval constructor rounds a lower endpoint down to the grid `2^(-B) Z` and an upper endpoint up to that grid. Addition and negation use the corresponding endpoint rules. Multiplication takes the minimum and maximum of all four endpoint products. Division requires that the entire denominator interval exclude zero, and multiplies by the reciprocal interval `[1/upper,1/lower]`. Every operation rounds outward again. These rules remain valid for negative endpoints and denominators.

For a nonnegative rational x, the integer

```
isqrt(floor(x*2^(2B)))
```

is exactly `floor(sqrt(x)*2^B)`. The square-root operation uses this for its lower endpoint, and increases its upper integer when the resulting squared dyadic is smaller than the upper input endpoint. Thus both bounds are outward. Integer powers use enclosing interval multiplication; dependency losses can enlarge an interval but cannot remove its true value.

The program isolates the unique real root of each cubic by exact rational bisection. The cubic discriminants are negative, and strict opposite endpoint signs are checked throughout. It similarly isolates the positive cube root `alpha=(b/a)^(1/3)` between 1 and 3. All denominator exclusions, positivity conditions, branch decisions and final width requirements are checked with rational comparisons. The command-line entry point refuses execution when assertions are disabled.

The saved calculation uses B=2048, 24 RF duplication steps, and Taylor order 60. No floating-point logarithm or square-root calculation contributes to its bounds.

## Carlson's symmetric integral and duplication

For nonnegative x,y,z with at most one zero, define

```
RF(x,y,z) = (1/2) integral_0^infinity
            ds / sqrt((s+x)(s+y)(s+z)).
```

This is the normalization of [DLMF 19.16.1 and 19.16.4](https://dlmf.nist.gov/19.16#E1). The integral converges under the stated domain restriction.

Put `lambda=sqrt(xy)+sqrt(yz)+sqrt(zx)`. The exact duplication formula is

```
RF(x,y,z) = RF((x+lambda)/4,(y+lambda)/4,(z+lambda)/4).
```

See [DLMF 19.26.18–19](https://dlmf.nist.gov/19.26#E18). Because the arguments here are divided by 4, no additional factor of 2 is applied. The implementation encloses each successive exact triple by outward interval arithmetic. After the first step all arguments are positive.

## Taylor integral and a proved remainder

For a final exact triple, let

```
A=(x+y+z)/3,  xi_1=1-x/A, xi_2=1-y/A, xi_3=1-z/A.
```

The substitution `s=A(t^(-2)-1)` in the defining integral gives

```
RF(x,y,z) = A^(-1/2) integral_0^1
            product_(i=1)^3 (1-xi_i*t^2)^(-1/2) dt.
```

The code obtains an exact rational upper bound delta for all `|xi_i|` and verifies `delta<1/4`. Write `c_j=binom(2j,j)/4^j`. Expanding the three factors and convolving their coefficient lists gives every coefficient through total degree N in `t^2`. Integration divides the degree-j coefficient by `2j+1`. Since delta<1, the series converge absolutely and uniformly on `[0,1]`, which justifies integration term by term.

The absolute value of the total degree-j coefficient is bounded by `beta_j*delta^j`, where

```
beta_j = (3/2)_j/j! = (2j+1)*binom(2j,j)/4^j.
```

This follows by multiplying three copies of the nonnegative series `(1-delta*t^2)^(-1/2)`. Put n=N+1. Since `beta_(j+1)/beta_j=(j+3/2)/(j+1)<=3/2` and `2j+1>=2n+1` for j>=n, the omitted integrated tail has absolute value at most

```
T = beta_n*delta^n / ((2n+1)*(1-3*delta/2)).
```

The denominator is positive. The code adds the interval `[-T,T]` to the enclosed truncated sum and divides by the enclosed positive `sqrt(A)`. This includes both truncation error and every arithmetic-rounding error. It does not infer an error estimate from numerical convergence.

## From the real cubic to a Legendre integral

For one of the models, write

```
f(x)=x^3+a2*x^2+a4*x+a6,
r = the unique real root,
R=sqrt(f'(r)),
beta=(3r+a2)/R,
m=(2-beta)/4.
```

The certified intervals verify `R>0` and `0<m<1`. Here m is the Legendre **parameter**, equal to the square of DLMF's modulus k. Expanding about r gives

```
f(r+R*t)=R^3*t*(t^2+beta*t+1).
```

For x>r, consider

```
I(x)=integral_x^infinity ds/(2*sqrt(f(s))).
```

Set `t=(x-r)/R=cot(phi/2)^2`, with `0<phi<pi`. Then

```
cos(phi)=(t-1)/(t+1),
sin(phi)=2*sqrt(t)/(1+t),
t^2+beta*t+1=(t+1)^2*(1-m*sin(phi)^2),
dt/sqrt(t*(t^2+beta*t+1))
    = -dphi/sqrt(1-m*sin(phi)^2).
```

It follows that

```
I(x)=F(phi|m)/(2*sqrt(R)).
```

For `0<=phi<=pi/2`, homogeneity and [DLMF 19.25.5](https://dlmf.nist.gov/19.25#E5) give

```
F(phi|m)=sin(phi)*RF(cos(phi)^2,1-m*sin(phi)^2,1).
```

The principal-range restriction matters. If t>1, the code uses this formula directly. If t<1, the same RF expression gives `F(pi-phi|m)`, and the code instead uses

```
F(phi|m)=2K(m)-F(pi-phi|m).
```

The relevant interval is checked to lie strictly on one side of t=1; no uncertain branch is chosen. Finally `K(m)=RF(0,1-m,1)` by [DLMF 19.25.1](https://dlmf.nist.gov/19.25#E1).

## Period and signs of the lifts

At x=r the preceding expression gives `I(r)=K(m)/sqrt(R)`. Traversing both branches of the real cubic therefore gives the positive real period

```
Omega=2K(m)/sqrt(R).
```

Near infinity, the uniformizing parameter for `dx/(2y)` satisfies `x(u)~u^(-2)` and `y(u)~-u^(-3)`. Thus a negative-y point has lift `u=I(x)` in `(0,Omega/2)`. The positive-y inverse has lift `u=Omega-I(x)` in `(Omega/2,Omega)`. The program checks every rational generator on the model and selects its lift using its exact y sign.

The formulas for xQ0 are taken from the exact birational-map computation in [CAS.md](../CAS.md). The corresponding displayed yQ0 values are strictly negative, so `uQ0=I(xQ0)`. The calculation checks `0<uQ0<Omega/2`. Knowledge of xQ0 alone would not distinguish the two signs; the negative-y identification is part of the preceding exact-map argument.

This fixes the lifts used by the inhomogeneous lattice calculation. It introduces no extra factor of 2 when converting to the model `w^2=4z^3-g2*z-g3`, because `z=x+a2/3`, `w=2y` and `dz/w=dx/(2y)`.

The lattice-area expression and its geometric interpretation are recorded separately in [INITIAL_BOUND.md](INITIAL_BOUND.md); the real-period and lift proof above does not rely on that interpretation.

## Exact rounding cells at the lattice scales

The output's advertised bound is only `width<10^(-400)`. That bound alone would **not** justify rounding after multiplication by `10^420`. The actual saved rational intervals are much narrower, and the lattice verifier checks their endpoints directly at every scale it uses.

For an interval `[l,h]` and C=10^s, it computes

```
a=floor(C*l+1/2), b=floor(C*h+1/2)
```

and requires a=b, equal to the recorded rounded integer n. This proves

```
n-1/2 <= C*l <= C*h < n+1/2.
```

Every enclosed true value therefore rounds to n under this convention, and its rounding error is at most 1/2. The saved four lattice chains contain 125 such endpoint checks, for the three basis logarithms, the real period and the target logarithm at each retained step. All 125 were checked by exact rational arithmetic, including the largest scale `C=10^420`. The correctness assertion is the checked cell containment, not the weaker summary width.

## Replay and trust boundary

From this directory, using ordinary Python with assertions enabled:

```sh
python3 certify_real_logs.py --output reproduced-real-logs.json
python3 verify_lattice_certificate.py --logs real_logs.json \
  --certificate lattice_reduction.json --output reproduced-lattice-check.json
```

The second command checks the saved rational interval rounding cells together with the lattice certificates. `real_logs.json` records the precision, duplication count, series order, rational endpoints and lift normalization. Its mathematical fields can be compared exactly across replays; Python version metadata may differ.

A normal-mode replay on Python 3.14.6 reproduced the original real-log JSON byte-for-byte. Independent high-precision Legendre evaluation and a different quadrature substitution were also used as sanity checks; those numerical checks supply no rigorous error certificate and are not premises of this proof. The rigorous enclosure rests on the exact outward arithmetic, the proved Taylor remainder and the cited analytic identities. It remains outside the Lean kernel.
