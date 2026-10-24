#!/usr/bin/env python3
"""Propose exact inhomogeneous lattice certificates using rational basis reduction.
The certificate verifies unimodularity and inverse-row distances, not LLL quality.
"""
from fractions import Fraction as Q
from math import isqrt, factorial
from pathlib import Path
import argparse, hashlib, json, sys
import sympy as s


def rq(v):return Q(int(v.p),int(v.q))
def rounded(itv,C):
    lo,hi=map(Q,itv)
    a=(lo*C+Q(1,2)).__floor__();b=(hi*C+Q(1,2)).__floor__()
    assert a==b,'increase real-log precision'
    return a

def exact_lll(rows):
    b=[list(map(int,row)) for row in rows]
    U=[[int(i==j) for j in range(4)] for i in range(4)]
    def gs():
        star=[];norm=[];mu=[[Q(0) for _ in range(4)] for _ in range(4)]
        for i in range(4):
            v=list(map(Q,b[i]))
            for j in range(i):
                mu[i][j]=sum(Q(b[i][h])*star[j][h] for h in range(4))/norm[j]
                v=[v[h]-mu[i][j]*star[j][h] for h in range(4)]
            star.append(v);norm.append(sum(z*z for z in v));assert norm[-1]>0
        return mu,norm
    k=1;count=0
    while k<4:
        count+=1;assert count<100000
        for j in range(k-1,-1,-1):
            mu,norm=gs();q=(mu[k][j]+Q(1,2)).__floor__()
            if q:
                b[k]=[b[k][h]-q*b[j][h] for h in range(4)]
                U[k]=[U[k][h]-q*U[j][h] for h in range(4)]
        mu,norm=gs()
        if norm[k]>=(Q(3,4)-mu[k][k-1]**2)*norm[k-1]:k+=1
        else:
            b[k],b[k-1]=b[k-1],b[k];U[k],U[k-1]=U[k-1],U[k];k=max(1,k-1)
    return s.Matrix(b),s.Matrix(U)

def main():
    if not __debug__: raise SystemExit('Assertions must be enabled')
    ap=argparse.ArgumentParser();ap.add_argument('--logs',type=Path,required=True);ap.add_argument('--output',type=Path,required=True);args=ap.parse_args()
    raw=args.logs.read_bytes();src=json.loads(raw)
    assert sum((Q(7**j,factorial(j)) for j in range(13)),Q(0))>1000
    assert sum((Q(11**j,factorial(j)) for j in range(16)),Q(0))>26892
    rows=[]
    for curve in src['curves']:
        bound=10**100;steps=[]
        for exponent in [420,30,20,16,14,12,11,10]:
            C=10**exponent
            v=[rounded(itv,C) for itv in curve['basis_logs_0_to_period']]
            omega=rounded(curve['real_period'],C);target=rounded(curve['uQ0'],C)
            basis=s.Matrix([[1,0,0,0],[0,1,0,0],[0,0,1,0],v+[omega]])
            reduced,U=exact_lll(basis.T.tolist())
            assert reduced==U*basis.T and U.det() in (-1,1)
            inverse=reduced.T.inv();coords=inverse*s.Matrix([0,0,0,target])
            distances=[]
            for j in range(4):
                y=rq(coords[j]);frac=y-y.__floor__();delta=min(frac,1-frac)
                norm=sum((rq(inverse[j,k])**2 for k in range(4)),Q(0))
                assert norm>0
                distances.append(delta*delta/norm)
            best=max(range(4),key=lambda j:distances[j]);d2=distances[best]
            qbest=None
            for q in range(exponent+1):
                if d2>3*bound*bound+(3*bound+1+10**q)**2:qbest=q
                else:break
            if qbest is None:continue
            square_upper=100*(Q(16)+Q(7,3)*(exponent-qbest))
            new=isqrt(square_upper.numerator//square_upper.denominator)
            if Q(new*new)==square_upper:new-=1
            assert (new+1)**2>=square_upper
            if new>=bound:continue
            def matrix(m):return [[str(int(m[i,j])) for j in range(4)] for i in range(4)]
            steps.append({'input_coefficient_bound':str(bound),'decimal_scale_exponent':exponent,
                'rounded_basis_logs':list(map(str,v)),'rounded_real_period':str(omega),
                'rounded_target':str(target),'row_basis_transformation':matrix(U),
                'reduced_row_basis':matrix(reduced),'det_transformation':int(U.det()),
                'selected_inverse_row':best,'distance_squared_lower':str(d2),
                'positive_scaled_log_lower_power10':qbest,'strict_M_squared_upper':str(square_upper),
                'output_closed_coefficient_bound':new})
            print('REDUCED',curve['pair'],str(bound),'->',new,'scale',exponent,'q',qbest,flush=True)
            bound=new
        assert steps and bound<100
        rows.append({'pair':curve['pair'],'steps':steps,'final_closed_coefficient_bound':bound})
    args.output.write_text(json.dumps({'status':'exact lattice certificates; uses documented initial bound and real-log enclosures, outside Lean',
        'python_version':sys.version,'sympy_version':s.__version__,'real_logs_sha256':hashlib.sha256(raw).hexdigest(),
        'initial_closed_coefficient_bound':str(10**100),'rounding_error_bound':'3 M+1 for noncentered lifts',
        'scalar_log_bounds':'log(10)<7/3; log(26892)+5<16, from positive exponential series',
        'curves':rows},indent=2)+'\n')

if __name__=='__main__':main()
