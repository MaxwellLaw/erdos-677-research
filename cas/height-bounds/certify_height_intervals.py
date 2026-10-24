#!/usr/bin/env python3
"""Exact-arithmetic certificate for four rank-three canonical height matrices.
Only Python standard-library integers/Fractions are used. No floating point.
The human proof of the real-logarithm and canonical-height bounds is in README.md.
"""
from fractions import Fraction as Q
from math import gcd, factorial
from pathlib import Path
import argparse, hashlib, json, sys

BITS, TERMS = 48, 40
BASIS = [
    [('5','6'),('13','38'),('-7','18')],
    [('12','-60'),('-4','92'),('78','-666')],
    [('221/4','3387/8'),('14','279'),('43','330')],
    [('23','-90'),('17','-102'),('-1','186')],
]

def outward(lo, hi):
    t = 1 << BITS
    return Q((lo*t).__floor__(),t), Q((hi*t).__ceil__(),t)

def log_unit(s):
    assert 1 <= s <= 2
    z = (s-1)/(s+1)
    z2 = z*z
    p, v = z, Q(0)
    for j in range(TERMS):
        v += 2*p/(2*j+1)
        p *= z2
    return v, v + 2*p/((2*TERMS+1)*(1-z2))

LOG2 = log_unit(Q(2))

def log_integer(n):
    assert n >= 1
    e = n.bit_length()-1
    sh = max(0,e-59)
    mant, rem = divmod(n,1<<sh)
    den = 1 << (e-sh)
    slo, shi = Q(mant,den), Q(mant+(rem>0),den)
    lo = e*LOG2[0] + log_unit(slo)[0]
    hi = e*LOG2[1] + log_unit(shi)[1]
    return outward(lo,hi)

def conv(a,b):
    c=[0]*(len(a)+len(b)-1)
    for i,x in enumerate(a):
        for j,y in enumerate(b): c[i+j]+=x*y
    return c

def check_bounds(c):
    _,a2,_,a4,a6=c['a_invariants']
    assert c['a_invariants'][0]==c['a_invariants'][2]==0
    F=[1,0,-2*a4,-8*a6,a4*a4-4*a2*a6]
    G=[0,4,4*a2,4*a4,4*a6]
    assert F==c['F_coefficients_p_descending']
    assert G==c['G_coefficients_p_descending']
    R=c['resultant_abs']; assert R>0
    for key,target in [('bezout_p7',[R]+[0]*7),('bezout_q7',[0]*7+[R])]:
        v=c[key]
        assert [a+b for a,b in zip(conv(v[:4],F),conv(v[4:],G))]==target
    C=max(sum(map(abs,F)),sum(map(abs,G)))
    D=max(sum(map(abs,c['bezout_p7'])),sum(map(abs,c['bezout_q7'])))
    assert C==c['upper_coefficient_C'] and D==c['lower_coefficient_D']
    return F,G,C,D

def on_curve(pt,a):
    x,y=pt; a2,a4,a6=a
    return y*y==x**3+a2*x*x+a4*x+a6

def add(p,q,a):
    assert p[0]!=q[0], 'only distinct-x input sums used'
    slope=(q[1]-p[1])/(q[0]-p[0])
    x=slope*slope-a[0]-p[0]-q[0]
    y=-p[1]+slope*(p[0]-x)
    assert on_curve((x,y),a)
    return x,y

def homog(coeff,p,q):
    return sum(v*p**(4-i)*q**i for i,v in enumerate(coeff))

def iterate(x,F,G,N):
    p,q=x.numerator,x.denominator
    for _ in range(N):
        f,g=homog(F,p,q),homog(G,p,q)
        d=gcd(f,g); assert d>0
        p,q=f//d,g//d
        assert q!=0, 'unexpected torsion/infinity in chosen inputs'
        if q<0: p,q=-p,-q
    assert gcd(p,q)==1 and q>0
    return p,q

def height_interval(pt,F,G,C,D,N):
    p,q=iterate(pt[0],F,G,N)
    h=log_integer(max(abs(p),q))
    lc,ld=log_integer(C),log_integer(D)
    scale=4**N
    itv=outward((h[0]-ld[1]/3)/scale,(h[1]+lc[1]/3)/scale)
    return itv,{'initial_point':list(map(str,pt)), 'iterate_x_numerator_hex':hex(p),
        'iterate_x_denominator_hex':hex(q), 'max_coordinate_bits':max(abs(p).bit_length(),q.bit_length()),
        'canonical_H_interval':list(map(str,itv))}

def det3(a):
    return (a[0][0]*(a[1][1]*a[2][2]-a[1][2]*a[2][1])
        -a[0][1]*(a[1][0]*a[2][2]-a[1][2]*a[2][0])
        +a[0][2]*(a[1][0]*a[2][1]-a[1][1]*a[2][0]))

def main():
    ap=argparse.ArgumentParser();ap.add_argument('constants',type=Path)
    ap.add_argument('--iterations',type=int,default=7);ap.add_argument('--lambda-lower',default='1/100')
    ap.add_argument('--output',type=Path,required=True); args=ap.parse_args()
    raw=args.constants.read_bytes();src=json.loads(raw); rows=[];lam=Q(args.lambda_lower)
    assert lam>0 and args.iterations>=0
    exp5_partial=sum((Q(5**j,factorial(j)) for j in range(11)),Q(0))
    assert exp5_partial==Q(7082479,48384) and exp5_partial>146
    assert all(c['upper_coefficient_C']<146**3 for c in src['curves'])
    for c,b in zip(src['curves'],BASIS,strict=True):
        F,G,C,D=check_bounds(c)
        a=(c['a_invariants'][1],c['a_invariants'][3],c['a_invariants'][4])
        pts=[tuple(map(Q,p)) for p in b]
        assert all(on_curve(p,a) for p in pts)
        matrix=[[None]*3 for _ in range(3)]; records=[]; diag=[]
        for i,p in enumerate(pts):
            itv,r=height_interval(p,F,G,C,D,args.iterations)
            r['label']=f'P{i+1}';records.append(r);diag.append(itv);matrix[i][i]=itv
        for i,j in [(0,1),(0,2),(1,2)]:
            itv,r=height_interval(add(pts[i],pts[j],a),F,G,C,D,args.iterations)
            r['label']=f'P{i+1}+P{j+1}';records.append(r)
            lo=(itv[0]-diag[i][1]-diag[j][1])/2
            hi=(itv[1]-diag[i][0]-diag[j][0])/2
            matrix[i][j]=matrix[j][i]=outward(lo,hi)
        mid=[[(lo+hi)/2 for lo,hi in row] for row in matrix]
        rad=[[(hi-lo)/2 for lo,hi in row] for row in matrix]
        rho=max(map(sum,rad))
        acheck=[[mid[i][j]-(lam+rho if i==j else 0) for j in range(3)] for i in range(3)]
        minors=[acheck[0][0],acheck[0][0]*acheck[1][1]-acheck[0][1]**2,det3(acheck)]
        assert all(v>0 for v in minors), 'Sylvester certificate failed: increase iterations or lower lambda'
        rows.append({'pair':c['pair'],'a_invariants':c['a_invariants'], 'basis':b,
            'height_records':records, 'pairing_intervals':[[list(map(str,v)) for v in row] for row in matrix],
            'max_radius_row_sum':str(rho),'midpoint_minus_lambda_plus_radius_identity':[[str(v) for v in row] for row in acheck],
            'leading_principal_minors':list(map(str,minors)),'certified_lambda':str(lam)})
        print('CERTIFIED',c['pair'],'lambda',lam,'N',args.iterations,'maxbits',max(r['max_coordinate_bits'] for r in records),flush=True)
    out={'status':'exact arithmetic certificate; human height theory; not Lean verified',
        'normalization':'H(P)=lim_N 4^-N log max(|num x(2^N P)|,den x(2^N P))',
        'conclusion':'H(sum_i m_i P_i) >= lambda * sum_i m_i^2 >= lambda * max_i |m_i|^2',
        'uniform_height_error_certificate':{'S':5,'base':146,'base_cubed':146**3,
            'exp5_positive_series_max_degree':10,'exp5_partial_sum':str(exp5_partial),
            'partial_sum_minus_base':str(exp5_partial-146),'meaning':'H(P)-h(x(P))<5 on all four curves'},
        'python_version':sys.version,'constants_sha256':hashlib.sha256(raw).hexdigest(),
        'iterations':args.iterations,'log_atanh_terms':TERMS,'interval_denominator_bits':BITS,'curves':rows}
    args.output.write_text(json.dumps(out,indent=2)+'\n')
    print('OUTPUT_SHA256',hashlib.sha256(args.output.read_bytes()).hexdigest(),flush=True)

if __name__=='__main__': main()
