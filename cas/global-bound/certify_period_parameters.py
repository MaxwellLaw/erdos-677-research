#!/usr/bin/env python3
"""Exact rational bounds for four real-period parameters. No floating point.
The period interpretation and K inequalities are human mathematics.
"""
from fractions import Fraction as Q
from math import isqrt
from pathlib import Path
import argparse, json, sys

MODELS=[((1,2),(-1,-65,261)),((1,5),(-1,-408,6912)),
        ((1,10),(1,-1633,97763)),((2,5),(1,-1633,32963))]
BITS=96

class I:
    def __init__(self,lo,hi=None):
        self.lo=Q(lo); self.hi=Q(lo if hi is None else hi)
        assert self.lo<=self.hi
    def __add__(self,o):
        o=as_i(o); return I(self.lo+o.lo,self.hi+o.hi)
    __radd__=__add__
    def __neg__(self): return I(-self.hi,-self.lo)
    def __sub__(self,o):return self+-as_i(o)
    def __rsub__(self,o):return as_i(o)+-self
    def __mul__(self,o):
        o=as_i(o); z=[a*b for a in (self.lo,self.hi) for b in (o.lo,o.hi)]
        return I(min(z),max(z))
    __rmul__=__mul__
    def __truediv__(self,o):
        o=as_i(o); assert o.lo*o.hi>0
        return self*I(1/o.hi,1/o.lo)
    def __rtruediv__(self,o):return as_i(o)/self
    def sqrt(self):
        assert self.lo>=0
        def lower(x):return isqrt((x.numerator << (2*BITS))//x.denominator)
        l,u=lower(self.lo),lower(self.hi)
        if Q(u*u,1<<(2*BITS))<self.hi:u+=1
        ans=I(Q(l,1<<BITS),Q(u,1<<BITS))
        assert ans.lo*ans.lo<=self.lo and ans.hi*ans.hi>=self.hi
        return ans
    def record(self):return [str(self.lo),str(self.hi)]

def as_i(x):return x if isinstance(x,I) else I(x)

def cubic(x,a):a2,a4,a6=a;return x**3+a2*x*x+a4*x+a6

def parameters(pair,a):
    a2,a4,a6=a
    disc=a2*a2*a4*a4-4*a4**3-4*a2**3*a6-27*a6*a6+18*a2*a4*a6
    assert disc<0
    lo,hi=Q(-128),Q(0)
    assert cubic(lo,a)<0<cubic(hi,a)
    for _ in range(BITS):
        mid=(lo+hi)/2
        if cubic(mid,a)<0:lo=mid
        else:hi=mid
    assert cubic(lo,a)<0<cubic(hi,a)
    r=I(lo,hi);c=3*r+a2;d=3*r*r+2*a2*r+a4
    R=d.sqrt();m=(2-c/R)/4
    assert R.lo>0 and 0<m.lo<=m.hi<Q(999,1000)
    # K(m)<=pi/(2 sqrt(1-m)), K(1-m)>=pi/2.
    # ratio^2 <= 4/(1-m) < 4000 < 64^2.
    assert 4/(1-m.hi)<4000<64**2
    return {'pair':pair,'a2_a4_a6':a,'cubic_discriminant':disc,
            'unique_real_root':r.record(),'fprime_at_root':d.record(),
            'R_sqrt_fprime':R.record(),'c_3r_plus_a2':c.record(),'m':m.record(),
            'm_strict_upper':'999/1000','real_period_squared_over_area_strict_upper':64}

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--output',type=Path,required=True);args=ap.parse_args()
    rows=[parameters(p,a) for p,a in MODELS]
    out={'status':'exact rational parameter certificate; period interpretation is human mathematics, not Lean',
         'python_version':sys.version,'bits':BITS,'period_formulas':{'Omega':'2 K(m)/sqrt(R)',
         'second_period':'Omega/2 + i K(1-m)/sqrt(R)',
         'area':'2 K(m) K(1-m)/R','ratio':'Omega^2/area=2 K(m)/K(1-m)<64'},'curves':rows}
    args.output.write_text(json.dumps(out,indent=2)+'\n')
    print('PASS: four curves, 0<m<999/1000, Omega^2/area<64 (using documented period formulas).')

if __name__=='__main__':
    if not __debug__: raise SystemExit("Assertions must remain enabled.")
    main()
