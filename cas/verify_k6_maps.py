#!/usr/bin/env python3
"""Exact rational polynomial checks for four k=6 cubic models.
This verifies map identities, not completeness of any integral-point search.
Requires SymPy 1.14.0. No floating-point arithmetic is used.
"""
import json
from math import lcm
import sympy as s
u,v,x,y,t=s.symbols('u v x y t')
Q=s.Rational
phi=lambda z:(z-1)*(z-9)*(z-25)
cases=[
 (1,2,[-1,-65,261],16*u+v-209,-672*u-36*v*v+1176*v-468,
  x*x-16*x+Q(9,4)*y+64,x*x-154*x+Q(105,4)*y+790,x*x-100*x+Q(201,4)*y+736),
 (1,5,[-1,-408,6912],24*(5*u+2*v-87),-1800*u*u+8400*u-1080*v*v+31920*v-37440,
  x*x-39*x+Q(9,2)*y+684,x*x-411*x+Q(57,2)*y+8748,x*x+21*x+Q(249,2)*y+7884),
 (1,10,[1,-1633,97763],500*u+247*v-9387,-43200*u*u+453600*u-10260*v*v+294840*v-694980,
  x*x-76*x+Q(33,4)*y+4864,x*x-838*x+Q(129,4)*y+62890,x*x+944*x+Q(993,4)*y+57544),
 (2,5,[1,-1633,32963],205*u+44*v-3129,-900*u*u-37800*u-2880*v*v+90720*v-49140,
  x*x-76*x+Q(21,4)*y+1624,x*x-784*x+Q(213,4)*y+20608,x*x-406*x+Q(501,4)*y+19474)
]

def num(z):return s.cancel(z).as_numer_denom()[0]
def rem(z,relation,var):return s.factor(s.rem(num(z),relation,var))
def checked(z,relation,var):
 r=rem(z,relation,var)
 assert r==0, r

out=[]
for a,b,cs,nx,ny,D,Nu,Nv in cases:
 F=s.expand(a*phi(v)-b*phi(u)); e=s.expand(y*y-x**3-cs[0]*x*x-cs[1]*x-cs[2])
 L=b*u-a*v-(b-a); fx=nx/L; fy=ny/L**2; gu=Nu/D; gv=Nv/D
 checked(e.subs({x:fx,y:fy},simultaneous=True),F,v)
 checked(gu.subs({x:fx,y:fy},simultaneous=True)-u,F,v)
 checked(gv.subs({x:fx,y:fy},simultaneous=True)-v,F,v)
 checked(F.subs({u:gu,v:gv},simultaneous=True),e,y)
 checked(fx.subs({u:gu,v:gv},simultaneous=True)-x,e,y)
 checked(fy.subs({u:gu,v:gv},simultaneous=True)-y,e,y)
 # Inverse denominator on the forward chart; retain exact rational numerator.
 den_comp=s.cancel(D.subs({x:fx,y:fy},simultaneous=True))
 den_num,den_den=den_comp.as_numer_denom()
 den_num=s.factor(s.rem(den_num,F,v))
 # dx/y = k dv / (b*Phi'(u)) on F=0.
 deriv=s.cancel((s.diff(fx,u)*s.diff(F,v)-s.diff(fx,v)*s.diff(F,u))/fy)
 k=s.cancel(deriv.subs({u:9,v:25}))
 checked(deriv-k,F,v)
 # On U>=49, V>=U, the inverse denominator after forwarding is strictly negative.
 p,q=s.symbols('p q', nonnegative=True)
 target_num=s.Poly(s.expand(den_num.subs({u:p+49,v:p+q+49})),p,q)
 assert all(c<=0 for c in target_num.coeffs()) and target_num.coeff_monomial(1)<0
 # The y coordinate is negative throughout U,V>=49.
 yn=s.Poly(s.expand(ny.subs({u:p+49,v:q+49})),p,q)
 assert all(c<=0 for c in yn.coeffs()) and yn.coeff_monomial(1)<0
 # Rational exceptional affine points of inverse: resultant factors.
 inv_res=s.factor(s.resultant(D,e,y))
 exception=[]
 for fac,powr in s.factor_list(inv_res,x)[1]:
  assert s.degree(fac,x) in (1,3) and s.Poly(fac,x).is_irreducible
  if s.degree(fac,x)==1:
   xx=s.solve(fac,x)[0]; yy=s.solve(D.subs(x,xx),y)[0]
   assert e.subs({x:xx,y:yy})==0
   exception.append([str(xx),str(yy)])
 # Algebraic limiting point as v/u -> t and u -> infinity.
 qx=s.cancel(s.limit(fx.subs(v,t*u),u,s.oo))
 qy=s.cancel(s.limit(fy.subs(v,t*u),u,s.oo))
 alg=a*t**3-b
 checked(e.subs({x:qx,y:qy},simultaneous=True),alg,t)
 checked(D.subs({x:qx,y:qy},simultaneous=True),alg,t)
 out.append({'a':a,'b':b,'minimal_a2_a4_a6':cs,
  'forward_x':str(fx),'forward_y':str(fy),'inverse_denominator':str(D),
  'inverse_u':str(gu),'inverse_v':str(gv),'six_map_checks':'PASS',
  'forward_L_zero_intersection':str(s.factor(F.subs(v,(b*u-b+a)/a))),
  'inverse_D_after_forward':str(den_num/den_den),
  'differential_dx_over_y_equals_k_dv_over_b_phi_prime_u':str(k),
  'inverse_D_zero_resultant':str(inv_res),'inverse_D_zero_rational_affine_points':exception,
  'point_at_infinity_qx':str(qx),'point_at_infinity_qy':str(qy),
  'point_at_infinity_checks':'PASS',
  'target_inverse_denominator_negative':'PASS', 'target_y_negative':'PASS'})
examples=[]
for a,b,U,V,n,m,X,Y in [(1,2,289,361,5,6,Q(199,9),Q(-2582,27)),(2,5,169,225,3,4,Q(5177,49),Q(-351630,343))]:
 case=next(c for c in cases if c[:2]==(a,b))
 _,_,cs,nx,ny,*_=case
 L=b*u-a*v-(b-a)
 assert a*phi(V)==b*phi(U)
 assert (nx/L).subs({u:U,v:V})==X
 assert (ny/L**2).subs({u:U,v:V})==Y
 assert (2*n+7)**2==U and (2*m+7)**2==V
 assert lcm(*range(n+1,n+7))==lcm(*range(m+1,m+7))
 assert n<m<n+6
 examples.append({'a':a,'b':b,'U':U,'V':V,'n':n,'m':m,'x':str(X),'y':str(Y),'lcm':lcm(*range(n+1,n+7)),'overlap':True})
print(json.dumps({'sympy_version':s.__version__,'integrality_counterexamples':examples,'scope':'Exact birational map identities only; no integer-point completeness claim','cases':out},indent=2))
