#!/usr/bin/env python3
"""Exact ideal arithmetic and Minkowski class-group mod-2 upper certificates."""
import ast
from certificate_io import finish
from fractions import Fraction as Q
import hashlib
import itertools
import json
from pathlib import Path
import re
from verify_export_algebra import determinant, prime
ROOT=Path(__file__).resolve().parent
IDENTITY=[[1,0,0],[0,1,0],[0,0,1]]

def literal(s):
    def go(n):
        if isinstance(n,ast.Constant) and type(n.value) is int:return Q(n.value)
        if isinstance(n,ast.List):return [go(x) for x in n.elts]
        if isinstance(n,ast.UnaryOp) and isinstance(n.op,ast.USub):return -go(n.operand)
        if isinstance(n,ast.BinOp) and isinstance(n.op,ast.Div):return go(n.left)/go(n.right)
        raise ValueError(ast.dump(n))
    return go(ast.parse(s,mode='eval').body)
def egcd(a,b):
    x0,y0,x1,y1=1,0,0,1
    while b:
        q=a//b;a,b=b,a-q*b;x0,x1=x1,x0-q*x1;y0,y1=y1,y0-q*y1
    if a<0:return -a,-x0,-y0
    return a,x0,y0

def hnf(vectors):
    a=[list(map(int,r)) for r in vectors];k=0
    for col in range(3):
        j=next((j for j in range(k,len(a)) if a[j][col]),None)
        if j is None:continue
        a[k],a[j]=a[j],a[k]
        for j in range(k+1,len(a)):
            if not a[j][col]:continue
            rp,rj=a[k][:],a[j][:];u,v=rp[col],rj[col];g,s,t=egcd(u,v)
            a[k]=[s*x+t*y for x,y in zip(rp,rj)]
            a[j]=[-(v//g)*x+(u//g)*y for x,y in zip(rp,rj)]
        if a[k][col]<0:a[k]=[-x for x in a[k]]
        for j in range(k):
            q=a[j][col]//a[k][col];a[j]=[x-q*y for x,y in zip(a[j],a[k])]
        k+=1
    assert k==3 and all(not any(r) for r in a[k:])
    return a[:k]
def member(v,H):
    v=list(v)
    for i in range(3):
        if v[i]%H[i][i]:return False
        q=v[i]//H[i][i];v=[x-q*y for x,y in zip(v,H[i])]
    return not any(v)
def multiply(a,b,table):return [sum(a[i]*b[j]*table[i][j][k] for i in range(3) for j in range(3)) for k in range(3)]
def ideal_mul(A,B,table):return hnf([multiply(a,b,table) for a in A for b in B])
def ideal_pow(A,n,table):
    assert n>=0;out=IDENTITY
    while n:
        if n%2:out=ideal_mul(out,A,table)
        n//=2
        if n:A=ideal_mul(A,A,table)
    return out

def rref(A,p):
    a=[[x%p for x in r] for r in A];piv=[];k=0
    for c in range(3):
        j=next((i for i in range(k,len(a)) if a[i][c]),None)
        if j is None:continue
        a[k],a[j]=a[j],a[k];u=pow(a[k][c],-1,p);a[k]=[x*u%p for x in a[k]]
        for i in range(len(a)):
            if i!=k:
                u=a[i][c];a[i]=[(x-u*y)%p for x,y in zip(a[i],a[k])]
        piv.append(c);k+=1
    return a[:k],piv

def poly_mul(a,b,p):
    c=[0]*(len(a)+len(b)-1)
    for i,x in enumerate(a):
        for j,y in enumerate(b):c[i+j]=(c[i+j]+x*y)%p
    return c

def charpoly(M,p):
    n=len(M);out=[0]*(n+1)
    for perm in itertools.permutations(range(n)):
        sign=(-1)**sum(perm[i]>perm[j] for i in range(n) for j in range(i+1,n));v=[sign]
        for i,j in enumerate(perm):v=poly_mul(v,[-M[i][j],1] if i==j else [-M[i][j]],p)
        for i,x in enumerate(v):out[i]=(out[i]+x)%p
    return out

def field_quotient(H,p,table):
    for e in IDENTITY:assert member([p*x for x in e],H)
    rows,piv=rref(H,p);free=[i for i in range(3) if i not in piv];f=len(free)
    assert 1<=f<=3 and abs(determinant(H))==p**f
    def reduce(v):
        v=[x%p for x in v]
        for row,c in zip(rows,piv):
            t=v[c];v=[(x-t*y)%p for x,y in zip(v,row)]
        return [v[i] for i in free]
    assert any(reduce(IDENTITY[0]))
    for j in free:
        a=IDENTITY[j];cols=[reduce(multiply(a,IDENTITY[i],table)) for i in free]
        M=[[cols[j][i] for j in range(f)] for i in range(f)]
        cp=charpoly(M,p)
        if f==1 or all(sum(c*pow(x,i,p) for i,c in enumerate(cp))%p for x in range(p)):
            assert cp[-1]==1
            return {'degree':f,'generator_order_coordinates':a,'irreducible_characteristic_polynomial_mod_p':cp}
    raise AssertionError(('No field quotient witness',p,H))

def parse(s,case):
    block=re.search(rf'BEGIN_CASE {case}\n(.*?)END_CASE {case}',s,re.S).group(1)
    matches=list(re.finditer(r'^(ORDER_BASIS|MINKOWSKI_UPPER|DECOMP|IDEAL|S_IDEALS|ANCHOR|RELATION)\b',block,re.M))
    out={'ideals':[],'decompositions':[],'relations':[]}
    for k,m in enumerate(matches):
        record=block[m.start():matches[k+1].start() if k+1<len(matches) else len(block)].strip();name=m.group(1);rest=record[len(name):].strip()
        if name in ('ORDER_BASIS','S_IDEALS'):out[name.lower()]=literal(rest)
        elif name in ('MINKOWSKI_UPPER','ANCHOR'):out[name.lower()]=int(rest)
        elif name=='DECOMP':out['decompositions'].append(list(map(int,rest.split())))
        elif name=='IDEAL':
            lead,mat=rest.split('[',1);i,p,e,n=map(int,lead.split());out['ideals'].append({'id':i,'p':p,'e':e,'norm':n,'basis':literal('['+mat)})
        elif name=='RELATION':
            lead,v=rest.split('[',1);i,h,b=map(int,lead.split());out['relations'].append({'id':i,'odd_power':h,'anchor_bit':b,'generator':literal('['+v)})
    return out

def main():
    if not __debug__:raise RuntimeError('Run without Python optimization')
    algebra_path=ROOT/'export_algebra_checks.json';alg=json.loads(algebra_path.read_text());results=[];all_hashes={}
    for case,arow in enumerate(alg['curves'],1):
        raw=ROOT/f'class_s_relations_{case}.result.json';d=json.loads(raw.read_text());assert d['success'] and not d['truncated'] and d['exit_code']==0
        row=parse(d['stdout'],case);all_hashes[raw.name]=hashlib.sha256(raw.read_bytes()).hexdigest()
        assert row['order_basis']==[[Q(x) for x in r] for r in arow['order_basis']]
        assert all(Q(x).denominator==1 for r in arow['order_multiplication_table'] for v in r for x in v)
        table=[[[int(Q(x)) for x in v] for v in r] for r in arow['order_multiplication_table']]
        B=row['minkowski_upper'];assert (27*B)**2>=64*abs(int(arow['order_discriminant']))
        primes=[p for p in range(2,B+1) if prime(p)]
        assert [p for p,n in row['decompositions']]==primes
        ideals=row['ideals'];assert [i['id'] for i in ideals]==list(range(1,len(ideals)+1))
        for item in ideals:
            assert all(q.denominator==1 for v in item['basis'] for q in v)
            item['basis']=H=hnf(item['basis']);p=item['p']
            assert p in primes and item['e']>=1 and determinant(H)==item['norm']
            for v in H:
                for e in IDENTITY:assert member(multiply(v,e,table),H)
            item['quotient_certificate']=field_quotient(H,p,table)
        for p,count in row['decompositions']:
            above=[i for i in ideals if i['p']==p];assert len(above)==count and len({str(i['basis']) for i in above})==count
            product=IDENTITY
            for item in above:product=ideal_mul(product,ideal_pow(item['basis'],item['e'],table),table)
            assert product==[[p*int(i==j) for j in range(3)] for i in range(3)]
        Sprimes=[2,3] if case==1 else [2,3,5]
        assert list(map(int,row['s_ideals']))==[i['id'] for i in ideals if i['p'] in Sprimes]
        anchor=row['anchor'];assert 0<=anchor<=len(ideals)
        expected=[i['id'] for i in ideals if i['norm']<=B]
        assert [r['id'] for r in row['relations']]==expected
        for rel in row['relations']:
            i,h,b=rel['id'],rel['odd_power'],rel['anchor_bit'];assert h>0 and h%2 and b in (0,1)
            target=ideal_pow(ideals[i-1]['basis'],h,table)
            if b:
                assert anchor;target=ideal_mul(target,ideal_pow(ideals[anchor-1]['basis'],h,table),table)
            alpha=rel['generator'];assert len(alpha)==3 and all(q.denominator==1 for q in alpha);alpha=list(map(int,alpha))
            principal=hnf([multiply(alpha,e,table) for e in IDENTITY]);assert principal==target
            rel['generator']=alpha;rel['verified_principal_ideal_basis']=principal
        cl_upper=int(anchor!=0);clS_upper=int(anchor!=0 and anchor not in row['s_ideals'])
        numS=len(row['s_ideals']);kernel_upper=1+numS-len(Sprimes)+clS_upper
        assert kernel_upper==[3,5,3,3][case-1]
        results.append({'case':case,'minkowski_upper':B,'number_of_rational_primes_checked':len(primes),'number_of_prime_ideals_checked':len(ideals),'number_of_minkowski_principal_relations':len(row['relations']),'class_mod_two_dimension_upper':cl_upper,'S_class_mod_two_dimension_upper':clS_upper,'S_prime_count':numS,'norm_square_KS2_dimension_upper':kernel_upper,'anchor_id':anchor,'anchor_over_S':bool(anchor and anchor in row['s_ideals']),'prime_ideals':ideals,'principal_relations':row['relations']})
    out={'status':'exact ideal certificates; uses standard algebraic number theory including Minkowski and S-unit exact sequence; not Lean verified','conclusion':'class/S-class mod-2 upper bounds and norm-square K(S,2) dimensions <= [3,5,3,3]','algebra_checks_sha256':hashlib.sha256(algebra_path.read_bytes()).hexdigest(),'raw_source_sha256':all_hashes,'curves':results}
    target=ROOT/'class_relation_checks.json';digest=finish(target,out)
    print('PASS: maximal-order prime decompositions, Minkowski generating set, principal relations; norm-kernel dimensions <=3,5,3,3')
    print('output_sha256',digest)
if __name__=='__main__':main()
