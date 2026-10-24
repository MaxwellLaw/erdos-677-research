#!/usr/bin/env python3
"""Independent finite-box verification using full finite-group translations.
No cyclic generator/discrete logarithm; primes differ from the primary sieve.
Only finite boxes are certified, conditional on the supplied global bounds.
"""
import argparse,ast,hashlib,json,sys
from fractions import Fraction
from math import gcd,isqrt,lcm
from pathlib import Path

Q=Fraction

def digest(data): return hashlib.sha256(data).hexdigest()
def object_hash(x):return digest(json.dumps(x,sort_keys=True,separators=(',',':')).encode())

def expression(text):
    node=ast.parse(text,mode='eval').body
    def check(n):
        if isinstance(n,ast.Constant):assert type(n.value) is int;return
        if isinstance(n,ast.Name):assert n.id in ('x','y');return
        if isinstance(n,ast.UnaryOp):assert isinstance(n.op,ast.USub);check(n.operand);return
        assert isinstance(n,ast.BinOp) and isinstance(n.op,(ast.Add,ast.Sub,ast.Mult,ast.Div,ast.Pow))
        check(n.left);check(n.right)
        if isinstance(n.op,ast.Pow):assert isinstance(n.right,ast.Constant) and 0<=n.right.value<=4
    check(node);return node

def evaluate(n,x,y,p=None):
    if isinstance(n,ast.Constant):return Q(n.value) if p is None else n.value%p
    if isinstance(n,ast.Name):return x if n.id=='x' else y
    if isinstance(n,ast.UnaryOp):return -evaluate(n.operand,x,y,p)
    a=evaluate(n.left,x,y,p)
    if isinstance(n.op,ast.Pow):v=a**n.right.value
    else:
        b=evaluate(n.right,x,y,p)
        if isinstance(n.op,ast.Add):v=a+b
        elif isinstance(n.op,ast.Sub):v=a-b
        elif isinstance(n.op,ast.Mult):v=a*b
        else:
            if b==0:raise ZeroDivisionError
            v=a/b if p is None else a*pow(b,-1,p)
    return v if p is None else v%p

class Curve:
    def __init__(self,coeff,p=None):self.a,self.b,self.c=coeff;self.p=p
    def norm(self,z):return z if self.p is None else z%self.p
    def divide(self,a,b):return Q(a)/b if self.p is None else a*pow(b,-1,self.p)%self.p
    def valid(self,P):
        return P is None or self.norm(P[1]**2-P[0]**3-self.a*P[0]**2-self.b*P[0]-self.c)==0
    def minus(self,P):return None if P is None else (P[0],self.norm(-P[1]))
    def plus(self,P,T):
        if P is None:return T
        if T is None:return P
        x,y=P;v,w=T
        if x==v and self.norm(y+w)==0:return None
        if x==v:
            assert y==w
            slope=self.divide(3*x*x+2*self.a*x+self.b,2*y)
        else:slope=self.divide(w-y,v-x)
        intercept=self.norm(y-slope*x)
        thirdx=self.norm(slope*slope-self.a-x-v)
        ans=(thirdx,self.norm(-slope*thirdx-intercept))
        assert self.valid(ans)
        return ans
    def times(self,k,P):
        if k<0:return self.times(-k,self.minus(P))
        # Left-to-right binary ladder, independent of the primary doubling loop.
        ans=None
        for bit in bin(k)[2:]:
            ans=self.plus(ans,ans)
            if bit=='1':ans=self.plus(ans,P)
        return ans
    def range_multiples(self,P,B):
        v=self.times(-B,P);out=[]
        for _ in range(2*B+1):out.append(v);v=self.plus(v,P)
        assert out[B] is None
        return out

def isprime(p):return p>1 and all(p%d for d in range(2,isqrt(p)+1))
def discr(c):
    a,b,d=c;return a*a*b*b-4*b**3-4*a**3*d-27*d*d+18*a*b*d

def reduced(P,p):
    if P is None:return None
    if any(z.denominator%p==0 for z in P):return None
    return tuple(z.numerator*pow(z.denominator,-1,p)%p for z in P)

def finite_data(coeff,basis,nodes,B,p):
    assert p>257 and isprime(p) and discr(coeff)%p!=0
    E=Curve(coeff,p);a,b,c=coeff
    roots={}
    for y in range(p):roots.setdefault(y*y%p,[]).append(y)
    points=[None]+[(x,y) for x in range(p) for y in roots.get((x*x*x+a*x*x+b*x+c)%p,[])]
    assert all(E.valid(P) for P in points) and len(points)==len(set(points))
    ids={P:i for i,P in enumerate(points)};N=len(points)
    Pb=[reduced(P,p) for P in basis];assert all(E.valid(P) for P in Pb)
    multiples=[E.range_multiples(P,B) for P in Pb[:2]]
    sum12=[[ids[E.plus(P,T)] for T in multiples[1]] for P in multiples[0]]
    step=[ids[E.plus(P,Pb[2])] for P in points]
    assert sorted(step)==list(range(N))
    trans=[ids[E.plus(P,E.times(-B,Pb[2]))] for P in points]
    translations=[]
    for _ in range(2*B+1):
        translations.append(trans);trans=[step[i] for i in trans]
    assert translations[B]==list(range(N))
    allow=[];exceptions=0
    for P in points:
        if P is None:allow.append(True);exceptions+=1;continue
        if evaluate(nodes[0],*P,p)==0:allow.append(True);exceptions+=1;continue
        u,v=(evaluate(node,*P,p) for node in nodes[1:])
        allow.append(all(z==0 or pow(z,(p-1)//2,p)==1 for z in (u,v)))
    two=sum(P is not None and P[1]==0 for P in points)
    meta={'prime':p,'group_order':N,'nonidentity_two_torsion_count':two,
      'noncyclic_witness':two==3,'exceptional_O_or_Dzero_retained':exceptions,
      'allowed_point_count':sum(allow),'points_sha256':object_hash(points),
      'allowed_points_sha256':object_hash([P for P,ok in zip(points,allow) if ok])}
    return sum12,translations,allow,meta

def coefficients(idx,L,B):
    i=idx%L;j=(idx//L)%L;k=idx//(L*L)
    return i-B,j-B,k-B

def exact_point(E,basis,cs):
    # Parenthesization differs from the primary sequential reconstruction.
    A,B,C=[E.times(n,P) for n,P in zip(cs,basis)]
    P=E.plus(A,E.plus(B,C));assert E.valid(P);return P

def exact_result(coeff,basis,nodes,pair,cs):
    E=Curve(coeff);P=exact_point(E,basis,cs)
    out={'coefficients':list(cs),'point':None if P is None else [str(z) for z in P]}
    if P is None:out['status']='elliptic_identity';return out
    if evaluate(nodes[0],*P)==0:out['status']='inverse_denominator_zero';return out
    U,V=[evaluate(node,*P) for node in nodes[1:]];out['inverse']=[str(U),str(V)]
    phi=lambda x:(x-1)*(x-9)*(x-25)
    assert pair[0]*phi(V)==pair[1]*phi(U)
    if U.denominator!=1 or V.denominator!=1:out['status']='noninteger_inverse';return out
    U,V=int(U),int(V);out['U_V']=[str(U),str(V)]
    if min(U,V)<49:out['status']='below_target';return out
    X,Y=isqrt(U),isqrt(V)
    if X*X!=U or Y*Y!=V:out['status']='nonsquare_inverse';return out
    if X%2!=1 or Y%2!=1:out['status']='even_square_root';return out
    n,m=(X-7)//2,(Y-7)//2;out['n_m']=[str(n),str(m)]
    C=lambda n:12*(2 if n%4>=2 else 1)*(5 if n%5==4 else 1)
    out['carry_equation']=pair[0]*C(m)==pair[1]*C(n)
    out['lcm_values']=[str(lcm(*range(n+1,n+7))),str(lcm(*range(m+1,m+7)))]
    if m<n+6:out['status']='gap_below_six';return out
    assert n>=0 and m>=n+6
    out['status']='collision' if out['lcm_values'][0]==out['lcm_values'][1] else 'lcm_unequal'
    return out

def small_test(coeff,basis,nodes,p):
    B=2;L=5;tables,trans,keep,_=finite_data(coeff,basis,nodes,B,p);E=Curve(coeff)
    for idx in range(L**3):
        i,j,k=idx%L,idx//L%L,idx//(L*L)
        cs=coefficients(idx,L,B);P=reduced(exact_point(E,basis,cs),p)
        slow=True
        if P is not None and evaluate(nodes[0],*P,p)!=0:
            vals=[evaluate(node,*P,p) for node in nodes[1:]]
            slow=all(v==0 or pow(v,(p-1)//2,p)==1 for v in vals)
        assert keep[trans[k][tables[i][j]]]==slow
    return {'prime':p,'box_bound':B,'exact_rational_comparisons':L**3,'pass':True}

def main():
    if not __debug__:raise SystemExit('Refuse disabled assertions')
    if hasattr(sys,'set_int_max_str_digits'):sys.set_int_max_str_digits(0)
    ap=argparse.ArgumentParser();ap.add_argument('--bounds',type=Path,required=True);ap.add_argument('--maps',type=Path,required=True);ap.add_argument('--basis-input',type=Path,required=True);ap.add_argument('--output',type=Path,required=True);args=ap.parse_args()
    bounds=json.loads(args.bounds.read_text());maps=json.loads(args.maps.read_text());basisdata=json.loads(args.basis_input.read_text())
    boundrows={tuple(r['pair']):r['final_closed_coefficient_bound'] for r in bounds['curves']}
    maprows={(r['a'],r['b']):r for r in maps['cases']}
    baserows={tuple(r['pair']):r for r in basisdata['curves']}
    assert set(boundrows)==set(maprows)==set(baserows)=={(1,2),(1,5),(1,10),(2,5)}
    result={'scope':'Exact exhaustive closed coefficient-box replay only; global completeness still requires the separate bound proof and full rational-group coverage.',
      'method':'complete E(Fp) point set, translation permutations, no cyclic generator/discrete log; descending primes >257',
      'inputs':{key:{'file':path.name,'sha256':digest(path.read_bytes())} for key,path in [('bounds',args.bounds),('maps',args.maps),('basis',args.basis_input)]},'curves':[]}
    for pair in sorted(boundrows):
        B=boundrows[pair];assert type(B) is int and 0<=B<=100;L=2*B+1
        coeff=baserows[pair]['a2_a4_a6'];assert coeff==maprows[pair]['minimal_a2_a4_a6']
        basis=[tuple(map(Q,P)) for P in baserows[pair]['basis']];assert len(basis)==3 and all(Curve(coeff).valid(P) for P in basis)
        nodes=[expression(maprows[pair][key]) for key in ['inverse_denominator','inverse_u','inverse_v']]
        primes=[p for p in range(503,257,-1) if isprime(p) and discr(coeff)%p][:30];assert len(primes)==30
        tests=[small_test(coeff,basis,nodes,primes[0])]
        remaining=None;records=[]
        for prime in primes:
            table,trans,keep,meta=finite_data(coeff,basis,nodes,B,prime)
            before=L**3 if remaining is None else len(remaining)
            if remaining is None:
                remaining=[];tested=0
                # k outermost, i innermost: distinct packing/order from primary sieve.
                for k in range(L):
                    tr=trans[k]
                    for j in range(L):
                        for i in range(L):
                            tested+=1
                            if keep[tr[table[i][j]]]:remaining.append(i+L*j+L*L*k)
                assert tested==L**3
            else:remaining=[idx for idx in remaining if keep[trans[idx//(L*L)][table[idx%L][idx//L%L]]]]
            meta.update({'tested':before,'retained':len(remaining),'retained_indices_sha256':object_hash(remaining)});records.append(meta)
            print('TRANSLATION_SIEVE',pair,prime,len(remaining),flush=True)
        triples=sorted(coefficients(idx,L,B) for idx in remaining)
        exact=[exact_result(coeff,basis,nodes,pair,cs) for cs in triples]
        counts={s:sum(v['status']==s for v in exact) for s in sorted({v['status'] for v in exact})}
        result['curves'].append({'pair':list(pair),'bound':B,'total_triples':L**3,'self_tests':tests,'sieves':records,'survivors':exact,'status_counts':counts})
        print('EXACT_RECONSTRUCTION',pair,counts,flush=True)
        args.output.write_text(json.dumps(result,indent=2)+'\n')
    print('DONE: finite boxes only; no unconditional global claim',flush=True)

if __name__=='__main__':main()
