#!/usr/bin/env python3
# Copyright (c) 2026 MaxwellLaw. Released under the Apache 2.0 license.
"""Independent replay of finite saturation witnesses; no discovery imports.
The mathematical good-reduction and group-law theorems are explained in README.
"""
import argparse, hashlib, itertools, json, math
from fractions import Fraction
from pathlib import Path

FIXED = [([1,2],[-1,-65,261],[[5,6],[13,38],[-7,18]]),
         ([1,5],[-1,-408,6912],[[12,-60],[-4,92],[78,-666]]),
         ([1,10],[1,-1633,97763],[[Fraction(221,4),Fraction(3387,8)],[14,279],[43,330]]),
         ([2,5],[1,-1633,32963],[[23,-90],[17,-102],[-1,186]])]

def is_prime(n):
    if n < 2:return False
    return all(n % k for k in range(2,math.isqrt(n)+1))

def discriminant(c):
    a,b,d=c
    # resultant(f,f') for monic cubic, with sign reversed
    return a*a*b*b+18*a*b*d-4*a*a*a*d-4*b*b*b-27*d*d

def evaluate(x,c,p):
    a,b,d=c
    return ((x+a)*x*x+b*x+d)%p

def cardinality(c,p):
    # Euler's criterion: for f(x)=0 there is one y, otherwise 0 or 2.
    total=1
    for x in range(p):
        f=evaluate(x,c,p)
        total += 1 if f==0 else (2 if pow(f,(p-1)//2,p)==1 else 0)
    return total

def on_curve(P,c,p):
    return P is None or (0<=P[0]<p and 0<=P[1]<p and P[1]*P[1]%p==evaluate(P[0],c,p))

def translate(P,g,c,p):
    """Addition by g via the line's third intersection; independent of discovery."""
    if P is None:return g
    x,y=P;u,v=g;a,b,d=c
    if x==u and (y+v)%p==0:return None
    if x==u:
        assert y==v
        slope=((3*x+2*a)*x+b)*pow(2*y,p-2,p)%p
    else:slope=(y-v)*pow((x-u)%p,p-2,p)%p
    intercept=(y-slope*x)%p
    # roots of f(X)-(slope*X+intercept)^2 sum to slope^2-a
    third=(slope*slope-a-x-u)%p
    return (third,(-slope*third-intercept)%p)

def reduction(P,p):
    result=[]
    for z in P:
        z=Fraction(z);assert z.denominator%p
        result.append(z.numerator*pow(z.denominator,p-2,p)%p)
    return tuple(result)

def determinant_permutations(a):
    answer=0
    for perm in itertools.permutations(range(3)):
        inv=sum(perm[i]>perm[j] for i in range(3) for j in range(i+1,3))
        answer+=(-1)**inv*math.prod(a[i][perm[i]] for i in range(3))
    return answer

def main():
    if not __debug__:raise SystemExit('Keep assertions enabled.')
    ap=argparse.ArgumentParser();ap.add_argument('certificate',type=Path);ap.add_argument('--output',type=Path);args=ap.parse_args()
    raw=args.certificate.read_bytes();doc=json.loads(raw)
    ells=[p for p in range(2,102) if is_prime(p)]
    assert doc['saturation_primes']==ells and len(doc['curves'])==4
    report=[]
    for row,(pair,c,basis) in zip(doc['curves'],FIXED,strict=True):
        assert row['pair']==pair and row['a2_a4_a6']==c
        assert [[Fraction(z) for z in P] for P in row['basis']]==basis
        for x,y in basis:assert y*y==x*x*x+c[0]*x*x+c[1]*x+c[2]
        ds=discriminant(c);assert ds!=0
        tors=row['torsion_prime_to_characteristic_certificate'];assert len(tors)==2
        for t in tors:
            p=t['prime'];assert is_prime(p) and p>3 and ds%p
            assert t['order']==cardinality(c,p)
            assert t['prime_times_order']==p*t['order']
        assert math.gcd(*(t['prime_times_order'] for t in tors))==1
        assert row['torsion_augmented_order_gcd']==1
        records={}
        for item in row['finite_group_records']:
            p=item['prime'];assert p not in records and is_prime(p) and p>3 and ds%p
            n=cardinality(c,p);assert n==item['order']
            g=tuple(item['generator']);assert on_curve(g,c,p)
            table=[];seen=set();P=None
            for i in range(n):
                assert on_curve(P,c,p) and P not in seen
                seen.add(P);table.append(P);P=translate(P,g,c,p)
            assert P is None and len(seen)==n
            # n distinct points from a group with exactly n points exhaust the group.
            assert hashlib.sha256(json.dumps(table,separators=(',',':')).encode()).hexdigest()==item['full_table_sha256']
            assert len(item['basis_indices'])==3
            for Q,j in zip(basis,item['basis_indices'],strict=True):
                assert 0<=j<n and table[j]==reduction(Q,p)
            records[p]=item
        certs=row['prime_saturation_certificates']
        assert [v['ell'] for v in certs]==ells
        for cert in certs:
            ell=cert['ell'];wits=cert['witnesses'];assert len(wits)==3
            assert len({w['auxiliary_prime'] for w in wits})==3
            mat=[]
            for w in wits:
                p=w['auxiliary_prime'];r=records[p]
                assert p!=ell and r['order']%ell==0
                expected=[j%ell for j in r['basis_indices']]
                assert w['residue_row']==expected;mat.append(expected)
            det=determinant_permutations(mat)
            assert det==cert['determinant'] and det%ell==cert['determinant_mod_ell'] and det%ell!=0
        assert max(records)==row['largest_auxiliary_prime_used']
        report.append({'pair':pair,'torsion_augmented_order_gcd':1,'verified_saturation_primes':ells,
            'cyclic_reductions_verified':len(records),'largest_auxiliary_prime':max(records)})
    result={'certificate_sha256':hashlib.sha256(raw).hexdigest(),'verifier_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
            'result':'PASS','scope':'exact finite field data only; reduction interpretation is a human theorem, not Lean; no rank upper or full saturation certificate',
            'curves':report}
    if args.output:args.output.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))

if __name__=='__main__':main()
