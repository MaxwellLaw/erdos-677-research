#!/usr/bin/env python3
# Copyright (c) 2026 MaxwellLaw. Released under the Apache 2.0 license.
"""Finite-field certificates for torsion-freeness and specified prime saturation.
Standard library only; this is not a rank upper bound or full saturation proof.
"""
from fractions import Fraction as Q
from math import gcd,isqrt
from pathlib import Path
import argparse,json,hashlib,sys

MODELS=[((1,2),(-1,-65,261),((5,6),(13,38),(-7,18)),(11,13)),
        ((1,5),(-1,-408,6912),((12,-60),(-4,92),(78,-666)),(7,11)),
        ((1,10),(1,-1633,97763),((Q(221,4),Q(3387,8)),(14,279),(43,330)),(7,19)),
        ((2,5),(1,-1633,32963),((23,-90),(17,-102),(-1,186)),(13,37))]

def prime(p):return p>=2 and all(p%d for d in range(2,isqrt(p)+1))
def factors(n):
    ans=[];d=2
    while d*d<=n:
        if n%d==0:
            ans.append(d)
            while n%d==0:n//=d
        d+=1
    if n>1:ans.append(n)
    return ans

def disc(c):
    a,b,d=c;return a*a*b*b-4*b**3-4*a**3*d-27*d*d+18*a*b*d

def points(c,p):
    roots={}
    for y in range(p):roots.setdefault(y*y%p,[]).append(y)
    a,b,d=c
    return [None]+[(x,y) for x in range(p) for y in roots.get((x**3+a*x*x+b*x+d)%p,[])]

def add(P,T,c,p):
    if P is None:return T
    if T is None:return P
    x,y=P;u,v=T;a,b,_=c
    if x==u:
        if (y+v)%p==0:return None
        assert y==v
        s=(3*x*x+2*a*x+b)*pow(2*y,-1,p)%p
    else:s=(v-y)*pow(u-x,-1,p)%p
    z=(s*s-a-x-u)%p
    return z,(-y+s*(x-z))%p

def mul(n,P,c,p):
    R=None
    while n:
        if n&1:R=add(R,P,c,p)
        n//=2
        if n:P=add(P,P,c,p)
    return R

def reduce(P,p):
    assert all(Q(z).denominator%p for z in P)
    return tuple(Q(z).numerator*pow(Q(z).denominator,-1,p)%p for z in P)

def rank(rows,l):
    a=[[x%l for x in row] for row in rows];r=0
    for col in range(3):
        k=next((k for k in range(r,len(a)) if a[k][col]),None)
        if k is None:continue
        a[r],a[k]=a[k],a[r];v=pow(a[r][col],-1,l)
        a[r]=[x*v%l for x in a[r]]
        for k in range(len(a)):
            if k!=r:
                s=a[k][col];a[k]=[(x-s*y)%l for x,y in zip(a[k],a[r])]
        r+=1
    return r

def det(a):
    return a[0][0]*(a[1][1]*a[2][2]-a[1][2]*a[2][1])-a[0][1]*(a[1][0]*a[2][2]-a[1][2]*a[2][0])+a[0][2]*(a[1][0]*a[2][1]-a[1][1]*a[2][0])

def cyclic_record(c,basis,p,pts):
    n=len(pts);qs=factors(n)
    P=next((P for P in pts[1:] if all(mul(n//q,P,c,p) is not None for q in qs)),None)
    if P is None:return None
    table=[];R=None
    for _ in range(n):table.append(R);R=add(R,P,c,p)
    assert R is None and len(set(table))==n and set(table)==set(pts)
    lookup={P:i for i,P in enumerate(table)}
    logs=[lookup[reduce(P,p)] for P in basis]
    digest=hashlib.sha256(json.dumps(table,separators=(',',':')).encode()).hexdigest()
    return {'prime':p,'order':n,'generator':list(P),'basis_indices':logs,'full_table_sha256':digest}

def main():
    if not __debug__:raise SystemExit('Assertions must remain enabled.')
    ap=argparse.ArgumentParser();ap.add_argument('--max-ell',type=int,default=101);ap.add_argument('--max-auxiliary',type=int,default=20000);ap.add_argument('--output',type=Path,required=True);args=ap.parse_args()
    ells=[l for l in range(2,args.max_ell+1) if prime(l)];assert ells
    output=[]
    for pair,c,basis,torsp in MODELS:
        selected={l:[] for l in ells};records={};tors=[]
        for p in torsp:
            assert prime(p) and p>5 and disc(c)%p
            n=len(points(c,p));tors.append({'prime':p,'order':n,'prime_times_order':p*n})
        assert gcd(*(v['prime_times_order'] for v in tors))==1
        for p in range(7,args.max_auxiliary+1):
            if not prime(p) or not disc(c)%p:continue
            pts=points(c,p);n=len(pts)
            targets=[l for l in ells if len(selected[l])<3 and l!=p and n%l==0]
            if not targets:continue
            row=cyclic_record(c,basis,p,pts)
            if row is None:continue
            used=False
            for l in targets:
                vals=[x%l for x in row['basis_indices']]
                old=[x['residue_row'] for x in selected[l]]
                if rank(old+[vals],l)>len(old):
                    selected[l].append({'auxiliary_prime':p,'residue_row':vals});used=True
                    if len(selected[l])==3:print('SATURATED',pair,l,flush=True)
            if used:records[p]=row
            if all(len(x)==3 for x in selected.values()):break
        certs=[]
        for l,w in selected.items():
            assert len(w)==3, (pair,l,'insufficient witnesses; increase auxiliary limit')
            determinant=det([x['residue_row'] for x in w]);assert determinant%l
            certs.append({'ell':l,'witnesses':w,'determinant':determinant,'determinant_mod_ell':determinant%l})
        output.append({'pair':list(pair),'a2_a4_a6':list(c),'basis':[[str(x) for x in P] for P in basis],
                       'torsion_prime_to_characteristic_certificate':tors,
                       'torsion_augmented_order_gcd':1,'finite_group_records':[records[p] for p in sorted(records)],
                       'prime_saturation_certificates':certs,'largest_auxiliary_prime_used':max(records)})
    data={'status':'finite-field witnesses verified exactly; human group/reduction interpretation, not Lean',
          'python_version':sys.version,'saturation_primes':ells,
          'scope':'torsion-free E(Q) and ell-saturation of the explicit rank-three subgroup at the listed ell; no rank upper bound, index bound, or all-prime saturation assertion',
          'curves':output}
    args.output.write_text(json.dumps(data,indent=2)+'\n')
    print('PASS:',len(ells),'saturation primes on all four curves; SHA256',hashlib.sha256(args.output.read_bytes()).hexdigest())

if __name__=='__main__':main()
