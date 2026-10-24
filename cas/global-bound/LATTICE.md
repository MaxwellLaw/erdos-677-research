# Exact inhomogeneous lattice-distance reduction

Mathematical proof of the exact arithmetic certificate, 2026-10-24. This note explains the certificate checked below. The executed residual enumeration is recorded separately in ENUMERATION.md.

Let `u1,u2,u3,Omega,uQ` denote the certified real lifts for a fixed curve,
with all basis lifts in `(0,Omega)`. The target branch has

```
L = sum_i mi*ui + m0*Omega - uQ,
M=max_i |mi|,
|m0|<=3M+1,
log|L|<16-M²/100.
```

The last inequality follows from the earlier upper bound if the finite
positive-series comparison `exp(11)>26892` has been certified. Also certify
`exp(7)>1000`, which implies `log(10)<7/3`.

Choose integers s,q with `0<=q<=s`, and put `C=10^s`. Certify nearest integers
`ai` to `C*ui`, `a0` to `C*Omega`, and `aQ` to `C*uQ`. A rational interval
contained in `[a-1/2,a+1/2]` suffices to prove each rounding error bound; it is
not necessary to assume a floating-point rounding was exact.

The column-basis matrix and target are

```
B = [[1,0,0,0],
     [0,1,0,0],
     [0,0,1,0],
     [a1,a2,a3,a0]],
t = [0,0,0,aQ]^T.
```

Require `a0!=0`. If an external LLL implementation proposes an integer matrix
U, check `det U=±1` and `Bred=B*U^T` exactly. The equality means the rows were
reduced before transposing. These checks prove lattice equality; no LLL quality
or Lovász-condition claim is needed for the subsequent distance certificate.

Put `A=Bred^-1`, checked by exact multiplication, and `y=A*t`. For every
coordinate j let `delta_j=dist(y_j,Z)`, calculated exactly from the numerator
and denominator of the rational y_j. The squared norm of row j of A is a
positive rational number. Define

```
d²=max_j delta_j² / sum_k A[j,k]².
```

For any lattice vector `v=Bred*z`, with integer z, Cauchy–Schwarz gives

```
delta_j <= |y_j-z_j|
         = |row_j(A)*(t-v)|
         <= norm(row_j(A))*norm(t-v).
```

Thus `norm(t-v)²>=d²` for every lattice vector. The bound remains valid when
some delta_j are zero. It makes no assumption about the reduced basis quality.

For the actual unknown coefficients, take `v=B*(m1,m2,m3,m0)^T`. Its first
three coordinates are mi. The last coordinate minus aQ differs from C*L by at
most

```
( |m1|+|m2|+|m3|+|m0|+1 )/2 <= 3M+1.
```

Consequently

```
norm(v-t)² <= 3M²+(C|L|+3M+1)².
```

Suppose an earlier certified step provides the closed bound `M<=B0` and the
exact rational checker verifies

```
d² > 3B0²+(3B0+1+10^q)².
```

If `C|L|<=10^q`, the two squared-distance bounds contradict one another.
Therefore `C|L|>10^q`, and combining logarithms with the analytic upper bound
proves

```
M² < 100*(16+(s-q)*log(10))
   <= 100*(16+(7/3)*(s-q)) = T.
```

The hypothesis `s-q>=0` is essential for the final substitution; omitting it
would reverse the required inequality when q>s. Equality when s=q is harmless
because the preceding inequality is strict.

To turn the strict rational square bound into a closed integer bound without
an off-by-one error, use

```
max_square=ceil(T)-1,
Bnext=isqrt(max_square).
```

Then every nonnegative integer M with M²<T satisfies M<=Bnext. Equivalently,
for `T=num/den>0`, compute
`max_square=(num+den-1)//den-1` entirely with integers. This handles T equal
to a perfect square as well as nonsquare rational values. Starting with the
weaker closed bound `B0=10^100` is valid under the proved strict initial
bound `M<10^100`.

Each successful step can use the preceding certified Bnext as its B0. The
final closed bound only justifies a finite coefficient box; complete exact
recovery and checking of that box remain separate obligations.

## Executed independent verification

The generated `lattice_reduction.json` was checked by
`verify_lattice_certificate.py`, an independent implementation using only
Python standard-library integers and Fractions. It performs its own exact
matrix determinant and Gauss–Jordan inversion, and verifies both products with
the identity matrix. It does not call SymPy or an LLL routine.

All **25 recorded steps passed**, yielding the closed bounds
`[60,60,62,64]` in the branch order `(1,2),(1,5),(1,10),(2,5)`.
The verifier checks source hashes, every input rounding cell, the stated lift
ranges, every unimodular matrix identity, the selected rational distance,
the strict threshold, the conditions on q,s, and the complete chain of integer
coefficient bounds. The positive series for exp(7) and exp(11) are checked
exactly as well.

The saved output `lattice_verification.json` has
SHA-256 `d5eb64ef11443eddc20aadfd5ade99c89237006e5359f7c483e6862b59613699`.
As a verification check, independently altered rounding, transformation,
distance, and output-bound fields were each rejected. No source or public
artifact was altered by those in-memory rejection checks.

Reproduction from this directory:

```
python3 verify_lattice_certificate.py \
  --logs real_logs.json \
  --certificate lattice_reduction.json \
  --output reproduced-lattice-verification.json
```

The input logarithm intervals and the analytic initial M bound retain their
separate human mathematical proofs. This finite checker does not establish
those analytic facts, complete the residual enumeration, or replace a Lean
proof.
