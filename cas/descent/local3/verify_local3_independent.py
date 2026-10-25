#!/usr/bin/env python3
"""Independent exact local-3 witness check using Sylvester resultants and minors."""
from pathlib import Path
from fractions import Fraction as Q
from math import lcm,isqrt
from itertools import combinations,permutations
import hashlib,json,argparse

def det(a):
    a=[[Q(x) for x in r] for r in a];v=Q(1)
    for j in range(len(a)):
        k=next((k for k in range(j,len(a)) if a[k][j]),None)
        if k is None:return Q(0)
        if k!=j:a[k],a[j]=a[j],a[k];v=-v
        t=a[j][j];v*=t
        for k in range(j+1,len(a)):
            z=a[k][j]/t
            a[k]=[x-z*y for x,y in zip(a[k],a[j])]
    return v

def norm(g):
    d=lcm(*(x.denominator for x in g));h=[int(x*d) for x in g]
    while len(h)>1 and h[-1]==0:h.pop()
    m=len(h)-1
    if m==0:return Q(h[0],d)**3
    f=[1,-1,-408,6912];h=h[::-1];n=3+m
    rows=[]
    for i in range(m):rows.append([0]*i+f+[0]*(n-i-4))
    for i in range(3):rows.append([0]*i+h+[0]*(n-i-len(h)))
    return det(rows)/d**3

def valuation(n):
    assert n
    k=0
    while n%3==0:k+=1;n//=3
    return k

def main():
    if not __debug__:raise SystemExit('Keep assertions enabled.')
    ap=argparse.ArgumentParser();ap.add_argument('certificate',type=Path);ap.add_argument('--output',type=Path);args=ap.parse_args()
    raw=args.certificate.read_bytes();c=json.loads(raw)
    assert c['cubic_ascending']==[6912,-408,-1,1]
    f=lambda x:x**3-x*x-408*x+6912
    df=lambda x:3*x*x-2*x-408
    assert all(f(x)%7 for x in range(7))
    N=c['root_precision'];assert N>=3
    roots=[int(r['residue']) for r in c['roots']];assert len(roots)==3
    root_proofs=[]
    for r in roots:
        s=valuation(df(r));assert s<N and f(r)%3**(N+s)==0
        # Strong Hensel: v(f(r))>2v(f'(r)) and root difference has v>=N.
        assert N+s>2*s
        root_proofs.append({'v_derivative':s,'f_divisible_by_3_to':N+s})
    assert all((roots[i]-roots[j])%3**N for i,j in combinations(range(3),2))
    rows=[];records=[]
    for item in c['candidates']:
        g=list(map(Q,item['coefficients']));assert len(g)==3
        n=norm(g);assert n==Q(item['norm']) and n>0 and n.denominator==1
        assert isqrt(n.numerator)**2==n.numerator
        rest=n.numerator
        for p in [2,3,5]:
            while rest%p==0:rest//=p
        assert rest==1
        # Recover the monic characteristic polynomial via four exact resultants.
        vals=[norm([Q(t)-g[0],-g[1],-g[2]]) for t in range(4)]
        d0=vals[0];a=vals[1]-1-d0;b=vals[2]-8-d0;d2=(b-2*a)/2;d1=a-d2
        assert vals[3]==27+9*d2+3*d1+d0
        cp=[d0,d1,d2,Q(1)];assert all(x.denominator==1 for x in cp)
        # Integrality and norm supported on S imply every prime-ideal factor lies above S.
        den=lcm(*(x.denominator for x in g));numer=[int(x*den) for x in g]
        local=[];bits=[]
        for r in roots:
            z=sum(numer[i]*r**i for i in range(3));v=valuation(z)
            assert v<N
            vd=valuation(den);u=(z//3**v)*pow(den//3**vd,-1,3)%3
            value={'valuation':v-vd,'unit_mod_3':u,'bits':[(v-vd)%2,u-1]}
            assert u in [1,2];local.append(value);bits+=value['bits']
        assert local==item['local_values'] and bits==item['bits']
        rows.append(bits);records.append({'norm':str(n),'monic_characteristic_polynomial':[str(x) for x in cp],'local_squareclasses':bits})
    assert len(rows)==4
    witness=next(cols for cols in combinations(range(6),4) if int(det([[r[i] for i in cols] for r in rows]))%2)
    assert c['local_image_rank']==4
    result={'status':'PASS','scope':'four integral S-supported norm-square classes with independent localization in split K tensor Q3; human Hensel/Kummer interpretation, not Lean',
      'source_sha256':hashlib.sha256(raw).hexdigest(),'root_proofs':root_proofs,'witnesses':records,'odd_four_by_four_minor_columns':witness,'rank':4}
    if args.output:args.output.write_text(json.dumps(result,indent=2)+'\n')
    print('PASS: four integral norm-square witnesses; three Hensel roots; independent rank-four local squareclasses.')

if __name__=='__main__':main()
