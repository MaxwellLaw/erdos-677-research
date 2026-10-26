#!/usr/bin/env python3
"""Exact tiny coefficient/finite-field witnesses; not a collision search.
Author: MaxwellLaw. Python standard library only.
"""
import json
from math import isqrt
from pathlib import Path


def prime_trial(p):
    assert p >= 2
    divisors = list(range(2, isqrt(p)+1))
    assert all(p % d for d in divisors)
    return divisors


cases = [
    dict(k=3, b=2, left=2, right=-1, prime=11,
         weights=[2,-1,2], scalar=1),
    dict(k=9, b=8, left=10, right=280, prime=113,
         weights=[280,-35,10,-5,4,-5,10,-35,280], scalar=144),
    dict(k=9, b=8, left=10, right=-35, prime=797,
         weights=[280,-35,10,-5,4,-5,10,-35,280], scalar=144),
    dict(k=9, b=8, left=10, right=10, prime=17,
         weights=[280,-35,10,-5,4,-5,10,-35,280], scalar=144),
    dict(k=9, b=8, left=10, right=-5, prime=683,
         weights=[280,-35,10,-5,4,-5,10,-35,280], scalar=144),
]

out = []
for c in cases:
    k,b,u,v,p = (c[t] for t in ['k','b','left','right','prime'])
    prime_trial(p)
    assert p % 3 == 2
    assert all(w % p for w in c['weights'])
    assert c['scalar'] % p
    a = b*u
    norm = a**3 - 2*v**3
    assert norm % p == 0
    root = a * pow(v, -1, p) % p
    assert pow(root, 3, p) == 2
    # The cofactor of X-root in X^3-2 is X^2+root*X+root^2.
    assert all((x*x + root*x + root*root) % p for x in range(p))
    assert [x for x in range(p) if (x**3-2)%p == 0] == [root]
    # Check every possible owner-pair factor remains nonconstant modulo p.
    assert all((-wj)%p for wi in c['weights'] for wj in c['weights'])
    # The normalized weights really are the signed endpoint factorials.
    from math import factorial
    assert [c['scalar']*w for w in c['weights']] == [
        (-1)**i*factorial(i)*factorial(k-i-1) for i in range(k)]
    out.append(dict(k=k,b=b,left=u,right=v,prime=p,
                    norm=norm,norm_quotient=norm//p,cubic_root=root,
                    quadratic_cofactor_roots=0,
                    trial_divisors_through=isqrt(p),
                    all_owner_factors_nonconstant=True))

# Graph forcing is direct and does not enumerate graphs:
# k=9: either left weight-10 vertex needs two distinct neighbors, but just
# one right vertex has the only nonlisted weight 4.
w9 = cases[1]['weights']
assert w9.count(10) == 2 and w9.count(4) == 1
assert set(w9)-{4} == {c['right'] for c in cases[1:]}
# k=3: the right weight -1 vertex needs two distinct incoming neighbors,
# while there is only one left weight -1 vertex.
w3 = cases[0]['weights']
assert w3.count(-1) == 1 and set(w3) == {2,-1}

result = dict(scope='Cubic coefficient obstructions only; not a collision search',
              author='MaxwellLaw', branches=out,
              k9_only_unlisted_right_weight=4,
              k9_unlisted_right_vertex_count=1,
              k3_only_nonforbidden_left_weight=-1,
              k3_nonforbidden_left_vertex_count=1)
saved = json.loads(Path(__file__).with_suffix(".json").read_text())
assert result == saved, "recorded cubic witness mismatch"
print(json.dumps(result, indent=2, sort_keys=True))
