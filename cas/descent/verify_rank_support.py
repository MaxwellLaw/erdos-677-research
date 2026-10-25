#!/usr/bin/env python3
"""Exact arithmetic used in the small-S support proof; not a Kummer axiom."""
from pathlib import Path
from math import isqrt
import json,hashlib,argparse
HERE=Path(__file__).resolve().parent
MODELS=[([-1,-65,261],[2,3],6),([-1,-408,6912],[2,3,5],120),([1,-1633,97763],[2,3,5],270),([1,-1633,32963],[2,3,5],90)]
def factor(n):
    out=[];p=2
    while p*p<=n:
        e=0
        while n%p==0:n//=p;e+=1
        if e:out.append([p,e])
        p+=1
    if n>1:out.append([n,1])
    return out

def result():
    source=HERE/'export_algebra_checks.json';data=json.loads(source.read_text());rows=[]
    for case,((a,b,c),S,index) in enumerate(MODELS,1):
        ar=data['curves'][case-1];assert ar['a2_a4_a6']==[a,b,c]
        assert int(ar['power_order_index'])==index
        assert all(p in S for p,e in factor(index))
        D=a*a*b*b-4*b**3-4*a**3*c-27*c*c+18*a*b*c
        assert int(ar['power_basis_discriminant'])==D
        factors=factor(abs(D));outside=[]
        for p,e in factors:
            if p in S:continue
            assert p>5 and e==1
            roots=[r for r in range(p) if (r**3+a*r*r+b*r+c)%p==0 and (3*r*r+2*a*r+b)%p==0]
            vals=[(r**3+a*r*r+b*r+c)%(p*p) for r in roots]
            assert all(v!=0 for v in vals)
            outside.append({'prime':p,'singular_roots':roots,'f_mod_p_squared':vals})
        rows.append({'case':case,'rational_S':S,'power_order_index':index,'power_discriminant':D,'factorization':factors,'excluded_singular_residue_classes':outside})
    return {'scope':'arithmetic supporting the written x-theta small-S valuation proof, not a Lean statement','algebra_sha256':hashlib.sha256(source.read_bytes()).hexdigest(),'curves':rows}

def main():
    if not __debug__:raise SystemExit('Keep assertions enabled.')
    ap=argparse.ArgumentParser();ap.add_argument('--write',action='store_true');args=ap.parse_args()
    text=json.dumps(result(),indent=2)+'\n';path=HERE/'rank_support.json'
    if args.write:path.write_text(text)
    else:assert path.read_text()==text
    print('PASS: all power-order indices supported on S and all excluded singular residue classes have odd f-valuation.')
if __name__=='__main__':main()
