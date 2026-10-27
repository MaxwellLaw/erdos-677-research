#!/usr/bin/env python3
# Copyright (c) 2026 MaxwellLaw. Released under the Apache 2.0 license.
"""Independent exact replay; imports no code from certificate discovery."""
from fractions import Fraction as Q
from math import gcd,isqrt,comb
from pathlib import Path
import argparse,hashlib,itertools,json

HERE=Path(__file__).resolve().parent
BOUNDS=HERE.parent/'height-bounds'
FIXED=[([1,2],[-1,-65,261]),([1,5],[-1,-408,6912]),([1,10],[1,-1633,97763]),([2,5],[1,-1633,32963])]

def product(a,b):
    ans=[Q(0)]*(len(a)+len(b)-1)
    for i in range(len(a)):
        for j in range(len(b)):ans[i+j]+=a[i]*b[j]
    return ans

def plus(a,b):
    n=max(len(a),len(b));return [(a[i] if i<len(a) else 0)+(b[i] if i<len(b) else 0) for i in range(n)]

def power(a,n):
    ans=[Q(1)]
    for _ in range(n):ans=product(ans,a)
    return ans

def poly_compose_linear(poly,L,S):
    ans=[Q(0)]
    for c in reversed(poly):
        ans=product(ans,[L,S]);ans[0]+=c
    while len(ans)>1 and ans[-1]==0:ans.pop()
    return ans+[Q(0)]*(5-len(ans))

def prime(p):return p>=2 and all(p%k for k in range(2,isqrt(p)+1))
def val(n,p):
    assert n!=0
    ans=0
    while n%p==0:ans+=1;n//=p
    return ans

def det(a):return a[0]*(a[4]*a[8]-a[5]*a[7])-a[1]*(a[3]*a[8]-a[5]*a[6])+a[2]*(a[3]*a[7]-a[4]*a[6])

def main():
    if not __debug__:raise SystemExit('Assertions must remain enabled.')
    ap=argparse.ArgumentParser();ap.add_argument('--output',type=Path);args=ap.parse_args()
    path=HERE/'small_height_certificate.json';raw=path.read_bytes();data=json.loads(raw)
    src=(BOUNDS/'duplication_bounds.json').read_bytes()
    heights_raw=(BOUNDS/'height_intervals.json').read_bytes();heights=json.loads(heights_raw)
    assert hashlib.sha256(src).hexdigest()==data['source_duplication_sha256']
    assert hashlib.sha256(heights_raw).hexdigest()==data['source_height_intervals_sha256']
    assert len(data['curves'])==4;summary=[]
    for row,(pair,abc),height in zip(data['curves'],FIXED,heights['curves'],strict=True):
        a,b,c=abc;assert row['pair']==pair==height['pair'] and row['a2_a4_a6']==abc
        F=[b*b-4*a*c,-8*c,-2*b,0,1];G=[4*c,4*b,4*a,4,0]
        assert row['F_ascending']==F and row['G_ascending']==G
        def f(x):return x**3+a*x*x+b*x+c
        def Fv(x):return x**4-2*b*x*x-8*c*x+b*b-4*a*c
        def Gv(x):return 4*f(x)
        # F = f'^2 - 4(a+2x) f, the link to singular reduction.
        df=[b,2*a,3];identity=plus(product(df,df),[-4*z for z in product([a,2],[c,b,a,1])])
        assert identity==F
        assert len(row['normalized_bezout_identities'])==2
        scalars=[]
        for i,ident in enumerate(row['normalized_bezout_identities']):
            assert ident['chart']==['bezout_p7','bezout_q7'][i]
            uu=ident['U_descending'][::-1];vv=ident['V_descending'][::-1];rr=ident['R'];assert rr>0
            expected=[0]*8;expected[7 if i==0 else 0]=rr
            assert plus(product(uu,F),product(vv,G))==expected;scalars.append(rr)
        R=scalars[0]*scalars[1]//gcd(*scalars);assert R==row['primitive_gcd_bound_before_point_restrictions']
        factor_product=1;localbound=1;seen=set()
        for loc in row['local_point_constraints']:
            p=loc['prime'];e=loc['resultant_exponent'];assert prime(p) and e>0 and p not in seen;seen.add(p)
            factor_product*=p**e
            if p<=5:
                M=p**(e+1);assert M==loc['modulus']
                square_flags=bytearray(M)
                for y in range(M):square_flags[(y*y)%M]=1
                count={}
                for x in range(M):
                    if not square_flags[f(x)%M]:continue
                    g=gcd(Fv(x),Gv(x));assert g!=0
                    v=val(g,p);assert v<=e;count[v]=count.get(v,0)+1
                assert {str(k):v for k,v in sorted(count.items())}==loc['gcd_valuation_counts']
                assert sum(count.values())==loc['eligible_x_count']
                vmax=max(count);assert vmax==loc['gcd_exponent_bound'];localbound*=p**vmax
            else:
                singular=[]
                for x in range(p):
                    if f(x)%p==0 and (3*x*x+2*a*x+b)%p==0:singular.append(x)
                assert singular==loc['singular_roots']
                residues=[f(x)%(p*p) for x in singular]
                assert residues==loc['f_at_roots_mod_p_squared'] and all(residues)
                assert loc['gcd_exponent_bound']==0
        assert factor_product==R and localbound==row['point_gcd_bound']
        assert row['archimedean_factor']==32
        leaf_count=0
        for label,polys in [('finite_chart',(F,G)),('reciprocal_chart',(F[::-1],G[::-1]))]:
            leaves=row['archimedean_bernstein_cover'][label];end=Q(-1)
            for leaf in leaves:
                L=Q(leaf['left']);U=Q(leaf['right']);assert L==end and L<U<=1;end=U
                assert leaf['polynomial'] in ('F','G') and leaf['sign'] in (-1,1)
                poly=polys[0 if leaf['polynomial']=='F' else 1]
                h=[32*leaf['sign']*z for z in poly];h[0]-=1
                actual=poly_compose_linear(h,L,U-L)
                bs=list(map(Q,leaf['bernstein_coefficients']));assert len(bs)==5 and min(bs)>=0
                reconstructed=[Q(0)]*5
                for j,bj in enumerate(bs):
                    term=product(power([0,1],j),power([1,-1],4-j))
                    reconstructed=plus(reconstructed,[bj*comb(4,j)*z for z in term])
                assert reconstructed==actual;leaf_count+=1
            assert end==1
        D=32*localbound;B=row['small_height_box_B'];assert D==row['stronger_lower_D']
        assert B>0 and 729*B**3>=1000*D and 729*B**3-1000*D==row['box_bound_integer_check']
        found=[];tested=0
        # Independent parameter order: every square denominator q <= B, all reduced p.
        for q in range(1,B+1):
            z=isqrt(q)
            if z*z!=q:continue
            for x in range(-B,B+1):
                if gcd(x,q)!=1:continue
                tested+=1
                W=x*x*x+a*x*x*q+b*x*q*q+c*q*q*q
                if W<0:continue
                Y=isqrt(W)
                if Y*Y==W:found.append((x,z,Y))
        assert tested==row['primitive_XZ_pairs_tested']
        pts=row['points_modulo_y_sign'];assert found==[(p['X'],p['Z'],p['Y_nonnegative']) for p in pts]
        for point in pts:
            x,z,y=point['X'],point['Z'],point['Y_nonnegative'];assert y>0
            xp=Q(x,z*z);yp=Q(y,z**3);assert yp*yp==f(xp)
            for recorded in point['doublings']:
                assert yp!=0
                slope=(3*xp*xp+2*a*xp+b)/(2*yp)
                xn=slope*slope-a-2*xp;yn=slope*(xp-xn)-yp;xp,yp=xn,yn
                assert yp*yp==f(xp)
                assert str(xp.numerator)==recorded['numerator'] and str(xp.denominator)==recorded['denominator']
            assert len(point['doublings'])==2
            N=max(abs(xp.numerator),xp.denominator)
            assert N**3-1024*D==int(point['height_test_N_cubed_minus_1024D'])>0
        intervals=[[Q(t) for t in interval] for line in height['pairing_intervals'] for interval in line]
        determinants=[det([intervals[i][mask>>i&1] for i in range(9)]) for mask in range(512)]
        lo,hi=map(Q,row['regulator_interval'])
        assert 0<lo<=min(determinants)<=max(determinants)<=hi<Q(8,5)
        summary.append({'pair':pair,'stronger_D':D,'small_height_box_B':B,'points_modulo_sign':len(pts),
                        'bernstein_leaves':leaf_count,'regulator_upper_strictly_below':'8/5'})
    result={'status':'PASS','certificate_sha256':hashlib.sha256(raw).hexdigest(),
        'verifier_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        'scope':'exact arithmetic replay; the written height proof gives global H>1/10; independent rank certificates are in cas/descent; this checker does not certify rank',
        'curves':summary}
    if args.output:args.output.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))

if __name__=='__main__':main()
