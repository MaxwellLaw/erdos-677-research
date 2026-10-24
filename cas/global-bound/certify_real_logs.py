#!/usr/bin/env python3
"""Dyadic interval certificates for real elliptic logarithms, using Carlson RF.
Every arithmetic operation is outward rounded by integer floor/ceiling.
The RF duplication identity and elliptic interpretation are documented inputs.
"""
from fractions import Fraction as Q
from math import isqrt, comb
from pathlib import Path
import argparse, json, sys

BITS=2048
DUPLICATIONS=24
ORDER=60
MODELS=[((1,2),(-1,-65,261)),((1,5),(-1,-408,6912)),((1,10),(1,-1633,97763)),((2,5),(1,-1633,32963))]
BASIS=[[(5,6),(13,38),(-7,18)],[(12,-60),(-4,92),(78,-666)],[(Q(221,4),Q(3387,8)),(14,279),(43,330)],[(23,-90),(17,-102),(-1,186)]]

class I:
    def __init__(self,lo,hi=None):
        lo,hi=Q(lo),Q(lo if hi is None else hi); assert lo<=hi
        d=1<<BITS
        self.lo=Q((lo*d).__floor__(),d);self.hi=Q((hi*d).__ceil__(),d)
    def __add__(self,o):
        o=as_i(o);return I(self.lo+o.lo,self.hi+o.hi)
    __radd__=__add__
    def __neg__(self):return I(-self.hi,-self.lo)
    def __sub__(self,o):return self+-as_i(o)
    def __rsub__(self,o):return as_i(o)+-self
    def __mul__(self,o):
        o=as_i(o);v=[a*b for a in (self.lo,self.hi) for b in (o.lo,o.hi)];return I(min(v),max(v))
    __rmul__=__mul__
    def __truediv__(self,o):
        o=as_i(o);assert o.lo*o.hi>0;return self*I(1/o.hi,1/o.lo)
    def __rtruediv__(self,o):return as_i(o)/self
    def sqrt(self):
        assert self.lo>=0
        def fl(x):return isqrt((x.numerator<<(2*BITS))//x.denominator)
        l,u=fl(self.lo),fl(self.hi)
        if Q(u*u,1<<(2*BITS))<self.hi:u+=1
        return I(Q(l,1<<BITS),Q(u,1<<BITS))
    def pow(self,n):
        assert n>=0
        if n==0:return I(1)
        if n%2:return self*self.pow(n-1)
        z=self.pow(n//2);return z*z
    def record(self):return [str(self.lo),str(self.hi)]
    def width(self):return self.hi-self.lo

def as_i(x):return x if isinstance(x,I) else I(x)

def conv(a,b):
    out=[I(0) for _ in range(ORDER+1)]
    for i,x in enumerate(a):
        for j,y in enumerate(b[:ORDER+1-i]):out[i+j]=out[i+j]+x*y
    return out

def rf(x,y,z):
    x,y,z=map(as_i,(x,y,z))
    assert min(x.lo,y.lo,z.lo)>=0 and sum(v.lo==0 for v in (x,y,z))<=1
    for _ in range(DUPLICATIONS):
        lam=(x*y).sqrt()+(y*z).sqrt()+(z*x).sqrt()
        x,y,z=(x+lam)/4,(y+lam)/4,(z+lam)/4
    A=(x+y+z)/3;assert A.lo>0
    xyz=[1-v/A for v in (x,y,z)]
    delta=max(max(abs(v.lo),abs(v.hi)) for v in xyz)
    assert delta<Q(1,4)
    polys=[]
    for v in xyz:
        p=I(1);poly=[]
        for j in range(ORDER+1):
            poly.append(Q(comb(2*j,j),4**j)*p);p=p*v
        polys.append(poly)
    coeff=conv(conv(polys[0],polys[1]),polys[2])
    series=sum((v/(2*j+1) for j,v in enumerate(coeff)),I(0))
    # Coefficient domination by (1-delta*t)^(-3/2).
    # beta_j=(3/2)_j/j!=(2j+1) choose(2j,j)/4^j.
    n=ORDER+1;beta=Q((2*n+1)*comb(2*n,n),4**n)
    tail=beta*delta**n/((2*n+1)*(1-Q(3,2)*delta))
    result=(series+I(-tail,tail))/A.sqrt()
    assert result.lo>0
    return result

def root_interval(a):
    a2,a4,a6=a
    def f(t):return t**3+a2*t*t+a4*t+a6
    lo,hi=Q(-128),Q(0);assert f(lo)<0<f(hi)
    for _ in range(BITS+8):
        mid=(lo+hi)/2
        if f(mid)<0:lo=mid
        else:hi=mid
    assert f(lo)<0<f(hi)
    return I(lo,hi)

def cube_root_ratio(a,b):
    lo,hi=Q(1),Q(3);assert a*lo**3<b<a*hi**3
    for _ in range(BITS+4):
        mid=(lo+hi)/2
        if a*mid**3<b:lo=mid
        else:hi=mid
    assert a*lo**3<b<a*hi**3
    return I(lo,hi)

def log_magnitude(x,r,R,m,K):
    t=(as_i(x)-r)/R;assert t.lo>0
    sinphi=2*t.sqrt()/(1+t)
    cos2=((t-1)/(t+1)).pow(2)
    F=sinphi*rf(cos2,1-m*sinphi*sinphi,I(1))
    if t.lo>1:res=F/(2*R.sqrt())
    else:
        assert t.hi<1
        res=(2*K-F)/(2*R.sqrt())
    assert res.lo>0
    return res

def main():
    global BITS,DUPLICATIONS,ORDER
    ap=argparse.ArgumentParser();ap.add_argument('--bits',type=int,default=BITS)
    ap.add_argument('--duplications',type=int,default=DUPLICATIONS);ap.add_argument('--order',type=int,default=ORDER)
    ap.add_argument('--output',type=Path,required=True);args=ap.parse_args()
    BITS,DUPLICATIONS,ORDER=args.bits,args.duplications,args.order
    assert BITS>=128 and DUPLICATIONS>=1 and ORDER>=1
    rows=[]
    for index,((a,b),coeff) in enumerate(MODELS):
        a2,a4,a6=coeff
        disc=a2*a2*a4*a4-4*a4**3-4*a2**3*a6-27*a6*a6+18*a2*a4*a6
        assert disc<0
        r=root_interval(coeff);R=(3*r*r+2*a2*r+a4).sqrt();m=(2-(3*r+a2)/R)/4
        assert 0<m.lo<m.hi<1
        K=rf(0,1-m,1);Kp=rf(0,m,1)
        omega=2*K/R.sqrt();area=2*K*Kp/R
        ratio=omega*omega/area;assert ratio.hi<64
        alpha=cube_root_ratio(a,b)
        numer=[16+alpha,120+48*alpha,500+247*alpha,205+44*alpha][index]
        xq=numer/(b-a*alpha)
        uq=log_magnitude(xq,r,R,m,K)
        logs=[]
        for x,y in BASIS[index]:
            assert Q(y)**2==Q(x)**3+a2*Q(x)**2+a4*Q(x)+a6
            u=log_magnitude(x,r,R,m,K)
            if y>0:u=omega-u
            assert 0<u.lo<u.hi<omega.lo
            logs.append(u.record())
        assert uq.hi<omega.lo/2
        assert max(omega.width(),uq.width(),*(Q(v[1])-Q(v[0]) for v in logs))<Q(1,10**400)
        rows.append({'pair':[a,b],'a2_a4_a6':coeff,'root':r.record(),'R':R.record(),'m':m.record(),
            'K':K.record(),'K_complement':Kp.record(),'real_period':omega.record(),
            'lattice_area':area.record(),'period_squared_over_area':ratio.record(),
            'alpha':alpha.record(),'xQ0':xq.record(),'uQ0':uq.record(),
            'basis':[[str(x),str(y)] for x,y in BASIS[index]],'basis_logs_0_to_period':logs,
            'strict_log_interval_width_upper':'1/10^400'})
        print('CERTIFIED real periods/logs',a,b,'width<1e-400',flush=True)
    args.output.write_text(json.dumps({'status':'rational interval arithmetic; human elliptic-integral theory; not Lean',
        'python_version':sys.version,'bits':BITS,'RF_duplications':DUPLICATIONS,'RF_series_order':ORDER,
        'normalization':'dx/(2y); all basis lifts in (0,Omega); Q0 negative-y lift in (0,Omega/2)',
        'curves':rows},indent=2)+'\n')

if __name__=='__main__':
    if not __debug__: raise SystemExit("Assertions must remain enabled.")
    main()
