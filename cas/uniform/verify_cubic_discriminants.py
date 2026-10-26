#!/usr/bin/env python3
"""Independent Euler-discriminant replay of the five cubic witnesses.
Author: MaxwellLaw. Does not import the root-enumeration checker.
"""
from math import factorial, lcm, isqrt
import json
cases=[(3,2,2,-1,11),(9,8,10,280,113),(9,8,10,-35,797),(9,8,10,10,17),(9,8,10,-5,683)]
out=[]
for k,b,u,v,p in cases:
    assert all(p%d for d in range(2,isqrt(p)+1))
    assert p%3==2
    norm=(b*u)**3-2*v**3
    assert norm%p==0
    residue=b*u*pow(v,-1,p)%p
    assert pow(residue,3,p)==2
    discriminant=(-3*residue*residue)%p
    assert pow(discriminant,(p-1)//2,p)==p-1
    weights=[(-1)**i*factorial(i)*factorial(k-i-1) for i in range(k)]
    assert all(w%p for w in weights)
    out.append(dict(k=k,p=p,norm=norm,quotient=norm//p,residue=residue,discriminant=discriminant,legendre=-1))
result={"branches":out,"Q":{k:lcm(*range(1,k+1))//k for k in [2,3,4,6,9]},"independence":"Exact trial division and Euler-criterion discriminant check; no finite-field root enumeration or original verifier imports"}
print(json.dumps(result,indent=2))
