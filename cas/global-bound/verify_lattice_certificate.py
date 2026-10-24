#!/usr/bin/env python3
"""Independent standard-library verifier for inhomogeneous lattice certificates.
No SymPy, no LLL implementation, and no floating point. This verifies exact
finite certificates, conditional on the documented analytic initial bound and
on the supplied certified real-logarithm intervals.
"""
from fractions import Fraction as Q
from math import factorial, isqrt
from pathlib import Path
import argparse
import hashlib
import json
import platform
import re

N = 4
PAIRS = [(1,2),(1,5),(1,10),(2,5)]

def integer(x):
    if isinstance(x, int) and not isinstance(x, bool):
        return x
    assert isinstance(x, str) and re.fullmatch(r"-?[0-9]+",x)
    return int(x)

def matrix(x):
    assert len(x)==N and all(len(row)==N for row in x)
    return [[integer(v) for v in row] for row in x]

def transpose(a):
    return [list(row) for row in zip(*a)]

def multiply(a,b):
    return [[sum((a[i][k]*b[k][j] for k in range(len(b))),Q(0))
             for j in range(len(b[0]))] for i in range(len(a))]

def determinant(a):
    m=[list(map(Q,row)) for row in a]
    ans=Q(1)
    for i in range(N):
        pivot=next((j for j in range(i,N) if m[j][i]),None)
        if pivot is None:return Q(0)
        if pivot!=i:m[i],m[pivot]=m[pivot],m[i];ans=-ans
        p=m[i][i];ans*=p
        for j in range(i+1,N):
            factor=m[j][i]/p
            m[j]=[m[j][k]-factor*m[i][k] for k in range(N)]
    return ans

def inverse(a):
    m=[[Q(v) for v in row]+[Q(int(i==j)) for j in range(N)]
       for i,row in enumerate(a)]
    for i in range(N):
        pivot=next((j for j in range(i,N) if m[j][i]),None)
        assert pivot is not None
        if pivot!=i:m[i],m[pivot]=m[pivot],m[i]
        p=m[i][i];m[i]=[v/p for v in m[i]]
        for j in range(N):
            if j!=i:
                factor=m[j][i]
                m[j]=[m[j][k]-factor*m[i][k] for k in range(2*N)]
    inv=[row[N:] for row in m]
    eye=[[Q(int(i==j)) for j in range(N)] for i in range(N)]
    assert multiply(a,inv)==multiply(inv,a)==eye
    return inv

def check_rounding(interval,C,n):
    assert len(interval)==2
    lo,hi=map(Q,interval)
    assert lo<=hi
    # This is the mathematical error requirement, independent of the generator's
    # tie-breaking convention or its use of floor(x+1/2).
    assert Q(n)-Q(1,2)<=C*lo<=C*hi<=Q(n)+Q(1,2)

def check_step(logs,step,previous):
    bound=integer(step["input_coefficient_bound"])
    assert bound==previous
    scale=integer(step["decimal_scale_exponent"])
    q=integer(step["positive_scaled_log_lower_power10"])
    assert 0<=q<=scale
    C=10**scale
    rounded=list(map(integer,step["rounded_basis_logs"]))
    assert len(rounded)==3
    for interval,n in zip(logs["basis_logs_0_to_period"],rounded,strict=True):
        check_rounding(interval,C,n)
    omega=integer(step["rounded_real_period"])
    target=integer(step["rounded_target"])
    check_rounding(logs["real_period"],C,omega)
    check_rounding(logs["uQ0"],C,target)
    assert omega!=0
    B=[[1,0,0,0],[0,1,0,0],[0,0,1,0],rounded+[omega]]
    U=matrix(step["row_basis_transformation"])
    redrows=matrix(step["reduced_row_basis"])
    det=determinant(U)
    assert det in [-1,1] and det==integer(step["det_transformation"])
    assert redrows==multiply(U,transpose(B))
    inv=inverse(transpose(redrows))
    y=[row[3]*target for row in inv]
    d2=[]
    for value,row in zip(y,inv,strict=True):
        remainder=value.numerator%value.denominator
        delta=Q(min(remainder,value.denominator-remainder),value.denominator)
        norm=sum((v*v for v in row),Q(0))
        assert norm>0
        d2.append(delta*delta/norm)
    selected=integer(step["selected_inverse_row"])
    assert 0<=selected<N
    claimed=Q(step["distance_squared_lower"])
    assert claimed==d2[selected]==max(d2)
    threshold=3*bound*bound+(3*bound+1+10**q)**2
    assert claimed>threshold
    T=100*(Q(16)+Q(7,3)*(scale-q))
    assert T==Q(step["strict_M_squared_upper"]) and T>0
    largest_square=(T.numerator+T.denominator-1)//T.denominator-1
    next_bound=isqrt(largest_square)
    assert next_bound==integer(step["output_closed_coefficient_bound"])
    assert 0<=next_bound<bound
    assert Q(next_bound*next_bound)<T<=Q((next_bound+1)**2)
    return next_bound, {"input_bound":str(bound),"scale":scale,"q":q,
                        "output_bound":next_bound,"verified_inverse_row":selected,
                        "strict_squared_upper":str(T),"all_exact_checks":True}

def main():
    if not __debug__:
        raise SystemExit("Do not disable certificate assertions with Python optimization")
    ap=argparse.ArgumentParser()
    ap.add_argument("--logs",type=Path,required=True)
    ap.add_argument("--certificate",type=Path,required=True)
    ap.add_argument("--output",type=Path)
    args=ap.parse_args()
    log_raw=args.logs.read_bytes();cert_raw=args.certificate.read_bytes()
    logs=json.loads(log_raw);cert=json.loads(cert_raw)
    assert cert["real_logs_sha256"]==hashlib.sha256(log_raw).hexdigest()
    assert [tuple(c["pair"]) for c in logs["curves"]]==PAIRS
    assert [tuple(c["pair"]) for c in cert["curves"]]==PAIRS
    assert integer(cert["initial_closed_coefficient_bound"])==10**100
    p7=sum((Q(7**j,factorial(j)) for j in range(13)),Q(0))
    p11=sum((Q(11**j,factorial(j)) for j in range(16)),Q(0))
    assert p7>1000 and p11>26892
    rows=[]
    for curve,c in zip(logs["curves"],cert["curves"],strict=True):
        omega_lo,omega_hi=map(Q,curve["real_period"])
        assert 0<omega_lo<=omega_hi
        assert len(curve["basis_logs_0_to_period"])==3
        for interval in curve["basis_logs_0_to_period"]:
            lo,hi=map(Q,interval)
            assert 0<lo<=hi<omega_lo
        qlo,qhi=map(Q,curve["uQ0"])
        assert 0<qlo<=qhi<omega_lo/2
        bound=10**100;steps=[]
        assert c["steps"]
        for step in c["steps"]:
            bound,record=check_step(curve,step,bound)
            steps.append(record)
        assert bound==integer(c["final_closed_coefficient_bound"])
        rows.append({"pair":c["pair"],"verified_steps":steps,
                     "final_closed_coefficient_bound":bound})
    out={"status":"PASS: every exact lattice step independently verified",
         "scope":"initial M bound and real logarithm enclosures remain documented mathematical inputs; no residual enumeration or Lean claim",
         "python":platform.python_version(),
         "uses_sympy":False,"checks_LLL_quality":False,
         "certificate_sha256":hashlib.sha256(cert_raw).hexdigest(),
         "real_logs_sha256":hashlib.sha256(log_raw).hexdigest(),
         "exp7_positive_partial_sum":str(p7),"exp7_positive_gap_above1000":str(p7-1000),
         "exp11_positive_partial_sum":str(p11),"exp11_positive_gap_above26892":str(p11-26892),
         "total_verified_steps":sum(len(c["verified_steps"]) for c in rows),
         "curves":rows}
    text=json.dumps(out,indent=2)+"\n"
    if args.output:args.output.write_text(text)
    else:print(text,end="")
    if args.output:
        print("PASS:",out["total_verified_steps"],"exact steps; final bounds",
              [c["final_closed_coefficient_bound"] for c in rows],flush=True)
        print("OUTPUT_SHA256",hashlib.sha256(args.output.read_bytes()).hexdigest(),flush=True)

if __name__=="__main__":main()
