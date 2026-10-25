#!/usr/bin/env python3
"""Exact candidate discovery for the (1,5) branch at Q_3; no CAS imports."""
from fractions import Fraction as Q
from math import gcd,lcm,isqrt
from itertools import permutations,combinations
from pathlib import Path
import json,hashlib
HERE=Path(__file__).resolve().parent
F=[6912,-408,-1,1]
def mul(a,b):
    c=[Q(0)]*5
    for i,x in enumerate(a):
        for j,y in enumerate(b):c[i+j]+=x*y
    for k in (4,3):
        for j in range(3):c[k-3+j]-=c[k]*F[j]
    return tuple(c[:3])
def add(a,b):return tuple(x+y for x,y in zip(a,b))
def scale(n,a):return tuple(n*x for x in a)
def evf(x):return x*x*x-x*x-408*x+6912
def deriv(x):return 3*x*x-2*x-408
def det(m):
    return sum((-1)**sum(p[i]>p[j] for i in range(3) for j in range(i+1,3))*m[0][p[0]]*m[1][p[1]]*m[2][p[2]] for p in permutations(range(3)))
B=[(Q(1),Q(0),Q(0)),(Q(0),Q(1),Q(0)),(Q(1,5),Q(71,120),Q(1,120))]
def matrix(a):
    columns=[mul(a,e) for e in [(1,0,0),(0,1,0),(0,0,1)]]
    return [[columns[j][i] for j in range(3)] for i in range(3)]
def norm(a):return det(matrix(a))
def charpoly(a):
    m=matrix(a);tr=sum(m[i][i] for i in range(3))
    tr2=sum(m[i][j]*m[j][i] for i in range(3) for j in range(3))
    return [-det(m),(tr*tr-tr2)/2,-tr,Q(1)]
def to_power(coords):
    z=(Q(0),Q(0),Q(0))
    for c,b in zip(coords,B):z=add(z,scale(c,b))
    return z
def vp(x):
    assert x
    k=0
    while x%3==0:k+=1;x//=3
    return k
def hensel(seed,N):
    s=vp(deriv(seed));k=s+1;r=seed
    assert evf(seed)%3**(2*s+1)==0
    initial={'seed':seed,'v_derivative':s,'f_seed':evf(seed),'derivative_seed':deriv(seed)}
    while k<N:
        good=[r+t*3**k for t in range(3) if evf(r+t*3**k)%3**(k+s+1)==0]
        assert len(good)==1
        r=good[0];k+=1
    assert evf(r)%3**(N+s)==0 and vp(deriv(r))==s
    return r,initial
def local(a,roots,N):
    d=lcm(*(x.denominator for x in a));aa=[int(x*d) for x in a];out=[]
    for r in roots:
        n=sum(aa[i]*r**i for i in range(3))%3**N
        assert n and vp(n)<N
        v=vp(n)-vp(d)
        u=(n//3**vp(n))*pow(d//3**vp(d),-1,3)%3
        assert u in (1,2)
        out.append({'valuation':v,'unit_mod_3':u,'bits':[v%2,u-1]})
    return out
def rank(rows):
    pivots={}
    for row in rows:
        n=sum(int(x)<<i for i,x in enumerate(row))
        while n:
            b=n.bit_length()-1
            if b in pivots:n^=pivots[b]
            else:pivots[b]=n;break
    return len(pivots)
def main():
    if not __debug__:raise RuntimeError("Assertions must remain enabled")
    assert not any(evf(x)%7==0 for x in range(7))
    cp=charpoly(B[2]);assert all(c.denominator==1 for c in cp)
    test=(Q(0),Q(0),Q(0))
    for c in reversed(cp):test=add(mul(test,B[2]),(c,0,0))
    assert test==(0,0,0)
    coords=[[-551,193,-217],[-154,174,-221],[-3319,-403,738],
       [48923,-2238,11240],[-337191,-127534,308272],[-685039,-116204,241024],
       [220703125,39062500,-82031250]]
    alphas=[to_power(v) for v in coords]
    norms=[norm(a) for a in alphas]
    assert [abs(n) for n in norms]==[Q(2**27)]*3+[Q(3**27)]*3+[Q(5**27)]
    N=80;rootdata=[hensel(seed,N) for seed in (0,6,1)];roots=[r for r,_ in rootdata]
    candidates=[]
    for i,j in [(0,1),(0,2),(3,4),(3,5)]:
        a=mul(alphas[i],alphas[j])
        if norm(a)<0:a=scale(-1,a)
        n=norm(a);assert n.denominator==1 and isqrt(n.numerator)**2==n
        loc=local(a,roots,N);bits=sum((r['bits'] for r in loc),[])
        candidates.append({'indices':[i+1,j+1],'coefficients':[str(c) for c in a],
          'norm':str(n),'local_values':loc,'bits':bits})
    rr=rank([r['bits'] for r in candidates]);assert rr==4
    out={'scope':'Exact four global norm-square S-supported witnesses with local-3 image rank four; human Kummer theory required for rank consequence; not Lean','generator_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),'cubic_ascending':F,'irreducible_modulus':7,'integral_basis_element':list(map(str,B[2])),
      'basis_element_monic_polynomial':list(map(str,cp)),'source_alphas_order_coordinates':coords,
      'source_alpha_norms':list(map(str,norms)),'root_precision':N,
      'roots':[{'residue':str(r),**w} for r,w in rootdata],
      'candidates':candidates,'local_image_rank':rr}
    p=HERE/'local3_candidates.json';p.write_text(json.dumps(out,indent=2)+'\n')
    print('LOCAL RANK',rr);print(json.dumps(candidates,indent=2));print('sha256',hashlib.sha256(p.read_bytes()).hexdigest())
if __name__=='__main__':main()
