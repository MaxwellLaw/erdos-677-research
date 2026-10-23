"""Exact algebra only; this does NOT compute all integral/rational points."""
import json
import platform
from fractions import Fraction
from math import gcd
import sympy as s

a, b, t, w, x, U, V, X = s.symbols('a b t w x U V X')
pairs = [(1, 2), (1, 5), (1, 10), (2, 5)]
Phi = lambda z: (z - 1) * (z - 9) * (z - 25)
H = lambda z: z**3 - 84*z - 160
assert s.expand(27*Phi(X**2) - 64*H((3*X**2-35)/4)) == 0
A, G, C = a*t**3-b, a*t**2-b, 192*(a*t-b)
Q = a*a*t**4 + 3*a*b*t**3 - 8*a*b*t**2 + 3*a*b*t + b*b
F = a*Phi(t*x+1)-b*Phi(x+1)
assert s.expand(F - x*(A*x*x-32*G*x+C)) == 0
assert s.expand((-32*G)**2 - 4*A*C - 256*Q) == 0
# Forward identity. F/x=0 implies w^2=Q when w=(A*x-16G)/8.
assert s.expand(((A*x-16*G)/8)**2-Q-A*(A*x*x-32*G*x+C)/64) == 0
# Inverse: x=8(w+2G)/A, y=t*x. Denominators A must be nonzero.
x_inverse = 8*(w+2*G)/A
assert s.cancel(A*x_inverse*x_inverse-32*G*x_inverse+C-64*(w*w-Q)/A) == 0
co = [a*a, 3*a*b, -8*a*b, 3*a*b, b*b]
qa,qb,qc,qd,qe = co
I = s.expand(12*qa*qe-3*qb*qd+qc**2)
J = s.expand(72*qa*qc*qe+9*qb*qc*qd-27*qa*qd**2-27*qb**2*qe-2*qc**3)
assert s.expand(I-49*a*a*b*b) == 0
assert s.expand(J+a*a*b*b*(243*(a*a+b*b)+200*a*b)) == 0
Delta = s.factor(4*I**3-J**2)
assert s.expand(Delta+243*a**4*b**4*(a-b)**2*(243*a*a+886*a*b+243*b*b)) == 0
rows = []
for av,bv in pairs:
    ev = {a:av,b:bv}
    # Irreducibility rules out A=0 for rational t.
    assert s.Poly(A.subs(ev),t).is_irreducible
    j = s.factor((6912*I**3/Delta).subs(ev))
    zero_discriminant = s.discriminant(av*Phi(V)+225*bv,V)
    assert zero_discriminant != 0
    assert j != 0 and s.denom(j) != 1
    rows.append(dict(a=av,b=bv,j=str(j),I=int(I.subs(ev)),J=int(J.subs(ev)),
                     U_zero_fiber_discriminant=int(zero_discriminant)))
assert s.resultant(X**2-1, (X+12)**2-1, X) == 20160
# These pairs satisfy center gcd/carry/disjoint filters only, NOT the curve.
def carry(n):
    return 12*(1 if n%4<2 else 2)*(5 if n%5==4 else 1)
examples=[]
for n in [0,60,120]:
    m=n+6; xx=2*n+7; yy=2*m+7
    assert gcd(xx,yy)==1 and carry(m)==2*carry(n)
    slope=Fraction(yy*yy-1,xx*xx-1)
    assert Phi(yy*yy)!=2*Phi(xx*xx)
    examples.append(dict(n=n,m=m,X=xx,Y=yy,center_gcd=1,
        projection_t=str(slope),curve_equation_satisfied=False))
print(json.dumps(dict(status='symbolic identities and invariants checked; no completeness certificate',
    python=platform.python_version(),sympy=s.__version__,quartic=str(Q),
    discriminant_numerator=str(Delta),curves=rows,
    gcd_carry_only_denominator_examples=examples),indent=2))
