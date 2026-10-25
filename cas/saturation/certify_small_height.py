#!/usr/bin/env python3
# Copyright (c) 2026 MaxwellLaw. Released under the Apache 2.0 license.
"""Exact stronger duplication bound and exhaustive small-height-box certificate.
Human height/reduction interpretation is in SMALL_HEIGHT.md, outside Lean.
"""
from fractions import Fraction as Q
from pathlib import Path
from math import gcd,lcm,isqrt,comb
import itertools,json,hashlib,sys

HERE=Path(__file__).resolve().parent
SOURCE=HERE.parent/'height-bounds/duplication_bounds.json'
HEIGHTS=HERE.parent/'height-bounds/height_intervals.json'

def conv(a,b):
    c=[0]*(len(a)+len(b)-1)
    for i,x in enumerate(a):
        for j,y in enumerate(b):c[i+j]+=x*y
    return c

def fac(n):
    out=[];p=2
    while p*p<=n:
        if n%p==0:
            e=0
            while n%p==0:n//=p;e+=1
            out.append((p,e))
        p+=1
    if n>1:out.append((n,1))
    return out

def ev(a,t):
    s=0
    for c in reversed(a):s=s*t+c
    return s

def bernstein(a,L,R):
    # Coefficients of polynomial a(L+(R-L)t), then degree-4 Bernstein coefficients.
    n=len(a)-1;d=R-L
    powers=[sum(a[j]*comb(j,k)*L**(j-k)*d**k for j in range(k,n+1)) for k in range(n+1)]
    return [sum(powers[k]*Q(comb(j,k),comb(n,k)) for k in range(j+1)) for j in range(n+1)]

def cover(F,G):
    leaves=[]
    def visit(L,R,depth):
        for label,poly in [('F',F),('G',G)]:
            for sign in [1,-1]:
                h=[32*sign*v for v in poly];h[0]-=1
                bs=bernstein(h,L,R)
                if min(bs)>=0:
                    leaves.append({'left':str(L),'right':str(R),'polynomial':label,'sign':sign,
                                   'bernstein_coefficients':[str(v) for v in bs]});return
        assert depth<25,(L,R)
        M=(L+R)/2;visit(L,M,depth+1);visit(M,R,depth+1)
    visit(Q(-1),Q(1),0)
    return leaves

def determinant_interval(mat):
    ans=[Q(0),Q(0)]
    for perm in itertools.permutations(range(3)):
        t=(Q(1),Q(1))
        for i in range(3):
            prods=[x*y for x in t for y in mat[i][perm[i]]];t=(min(prods),max(prods))
        if sum(perm[i]>perm[j] for i in range(3) for j in range(i+1,3))%2:t=(-t[1],-t[0])
        ans=[x+y for x,y in zip(ans,t)]
    return ans

def main():
    if not __debug__:raise SystemExit('Assertions must remain enabled.')
    src=SOURCE.read_bytes();data=json.loads(src);height_data=json.loads(HEIGHTS.read_bytes());out=[]
    for row,hr in zip(data['curves'],height_data['curves'],strict=True):
        pair=row['pair'];assert pair==hr['pair']
        _,a,_,b,c=row['a_invariants'];F=[b*b-4*a*c,-8*c,-2*b,0,1];G=[4*c,4*b,4*a,4,0]
        assert F[::-1]==row['F_coefficients_p_descending'] and G[::-1]==row['G_coefficients_p_descending']
        R=row['resultant_abs'];bez=[]
        for name,position in [('bezout_p7',0),('bezout_q7',7)]:
            coeffs=row[name];common=gcd(R,*coeffs);rr=R//common;uu=[z//common for z in coeffs[:4]];vv=[z//common for z in coeffs[4:]]
            got=[x+y for x,y in zip(conv(uu,F[::-1]),conv(vv,G[::-1]))];expected=[0]*8;expected[position]=rr;assert got==expected
            bez.append({'chart':name,'R':rr,'U_descending':uu,'V_descending':vv})
        Rg=lcm(*(z['R'] for z in bez));local=[];gmax=1
        for p,e in fac(Rg):
            if p<=5:
                mod=p**(e+1);squares={y*y%mod for y in range(mod)};counts={};allowed=0
                for x in range(mod):
                    if (x**3+a*x*x+b*x+c)%mod not in squares:continue
                    ff=ev(F,x)%mod;gg=ev(G,x)%mod;v=0
                    while ff%p==0 and gg%p==0:
                        v+=1;ff//=p;gg//=p
                        assert v<=e
                    counts[v]=counts.get(v,0)+1;allowed+=1
                v=max(counts);gmax*=p**v
                local.append({'prime':p,'resultant_exponent':e,'modulus':mod,'eligible_x_count':allowed,
                              'gcd_valuation_counts':{str(k):v for k,v in sorted(counts.items())},'gcd_exponent_bound':v})
            else:
                singular=[x for x in range(p) if (x**3+a*x*x+b*x+c)%p==0 and (3*x*x+2*a*x+b)%p==0]
                assert all((x**3+a*x*x+b*x+c)%(p*p)!=0 for x in singular)
                local.append({'prime':p,'resultant_exponent':e,'singular_roots':singular,
                    'f_at_roots_mod_p_squared':[(x**3+a*x*x+b*x+c)%(p*p) for x in singular],
                    'gcd_exponent_bound':0})
        arch={'finite_chart':cover(F,G),'reciprocal_chart':cover(F[::-1],G[::-1])}
        D=32*gmax
        B=1
        while 729*B**3<1000*D:B+=1
        pts=[];tested=0
        for z in range(1,isqrt(B)+1):
            for x in range(-B,B+1):
                if gcd(x,z)!=1:continue
                tested+=1;w=x**3+a*x*x*z*z+b*x*z**4+c*z**6
                if w<0:continue
                y=isqrt(w)
                if y*y!=w:continue
                assert y>0 # no affine rational 2-torsion occurs in the exhaustive box
                p,q=x,z*z;iters=[]
                for k in range(2):
                    fp=sum(F[i]*p**i*q**(4-i) for i in range(5));gp=sum(G[i]*p**i*q**(4-i) for i in range(5))
                    gg=gcd(fp,gp);assert gg>0
                    p,q=fp//gg,gp//gg
                    if q<0:p,q=-p,-q
                    assert q>0
                    iters.append({'numerator':str(p),'denominator':str(q)})
                N=max(abs(p),q);margin=N**3-1024*D;assert margin>0,(pair,x,z,y)
                pts.append({'X':x,'Z':z,'Y_nonnegative':y,'doublings':iters,'height_test_N_cubed_minus_1024D':str(margin)})
        mat=[[[Q(v) for v in interval] for interval in line] for line in hr['pairing_intervals']]
        reg=determinant_interval(mat);assert 0<reg[0]<=reg[1]<Q(8,5)
        out.append({'pair':pair,'a2_a4_a6':[a,b,c],'F_ascending':F,'G_ascending':G,
            'normalized_bezout_identities':bez,'primitive_gcd_bound_before_point_restrictions':Rg,
            'local_point_constraints':local,'point_gcd_bound':gmax,'archimedean_factor':32,
            'archimedean_bernstein_cover':arch,'stronger_lower_D':D,'small_height_box_B':B,
            'box_bound_integer_check':729*B**3-1000*D,'primitive_XZ_pairs_tested':tested,
            'points_modulo_y_sign':pts,'regulator_interval':[str(z) for z in reg]})
        print('PASS',pair,'D',D,'B',B,'points',len(pts),'arch leaves',sum(len(z) for z in arch.values()),flush=True)
    report={'status':'exact arithmetic certificate; human elliptic-curve and height interpretation, not Lean',
            'python_version':sys.version,'source_duplication_sha256':hashlib.sha256(src).hexdigest(),
            'source_height_intervals_sha256':hashlib.sha256(HEIGHTS.read_bytes()).hexdigest(),
            'scope':'H(P)>1/10 for nonzero rational points; together with the finite-prime certificate, complete saturation of the given rank-three subgroup; rank upper bound not proved here',
            'curves':out}
    path=HERE/'small_height_certificate.json';path.write_text(json.dumps(report,indent=2)+'\n')
    print('SHA256',hashlib.sha256(path.read_bytes()).hexdigest())

if __name__=='__main__':main()
