#!/usr/bin/env python3
"""Exact residual box sieve. See README for mathematics and completeness scope."""
from fractions import Fraction as Q
from math import isqrt, lcm
from pathlib import Path
from collections import Counter
import argparse, ast, hashlib, json, sys

MODELS=[
 ((1,2),(-1,-65,261),((5,6),(13,38),(-7,18)),
  (4,-64,9,256),(4,-616,105,3160),(4,-400,201,2944)),
 ((1,5),(-1,-408,6912),((12,-60),(-4,92),(78,-666)),
  (4,-156,18,2736),(4,-1644,114,34992),(4,84,498,31536)),
 ((1,10),(1,-1633,97763),((Q(221,4),Q(3387,8)),(14,279),(43,330)),
  (4,-304,33,19456),(4,-3352,129,251560),(4,3776,993,230176)),
 ((2,5),(1,-1633,32963),((23,-90),(17,-102),(-1,186)),
  (4,-304,21,6496),(4,-3136,213,82432),(4,-1624,501,77896)),
]

def canonical_hash(obj):
    return hashlib.sha256(json.dumps(obj,separators=(',',':'),sort_keys=True).encode()).hexdigest()

def point_record(P):return None if P is None else [str(P[0]),str(P[1])]

def on_curve(P,cs,p=None):
    if P is None:return True
    x,y=P;a,b,c=cs;z=y*y-x*x*x-a*x*x-b*x-c
    return z==0 if p is None else z%p==0

def add(P,S,cs,p=None):
    if P is None:return S
    if S is None:return P
    x,y=P;u,v=S;a,b,_=cs
    norm=(lambda z:z) if p is None else (lambda z:z%p)
    if x==u:
        if norm(y+v)==0:return None
        assert y==v
        num,den=3*x*x+2*a*x+b,2*y
    else:num,den=v-y,u-x
    slope=Q(num)/den if p is None else num*pow(den,-1,p)%p
    z=norm(slope*slope-a-x-u)
    ans=(z,norm(-y+slope*(x-z)))
    assert on_curve(ans,cs,p)
    return ans

def neg(P,p=None):
    if P is None:return None
    return (P[0],-P[1] if p is None else -P[1]%p)

def mul(n,P,cs,p=None):
    if n<0:return mul(-n,neg(P,p),cs,p)
    out=None
    while n:
        if n&1:out=add(out,P,cs,p)
        n//=2
        if n:P=add(P,P,cs,p)
    return out

def reduce_point(P,p):
    if P is None:return None
    x,y=map(Q,P)
    if x.denominator%p==0 or y.denominator%p==0:return None
    return (x.numerator*pow(x.denominator,-1,p)%p,
            y.numerator*pow(y.denominator,-1,p)%p)

def polyval(coeff,P):
    x,y=P;a,b,c,d=coeff
    return a*x*x+b*x+c*y+d

def disc(cs):
    a,b,c=cs
    return a*a*b*b-4*b**3-4*a**3*c-27*c*c+18*a*b*c

def prime(n):return n>=2 and all(n%d for d in range(2,isqrt(n)+1))

def factors(n):
    out=[];d=2
    while d*d<=n:
        if n%d==0:
            out.append(d)
            while n%d==0:n//=d
        d+=1
    if n>1:out.append(n)
    return out

# Parse only elementary polynomial syntax from the fixed map JSON; never eval.
def clean(d):return {m:c for m,c in d.items() if c}
def padd(a,b):
    out=dict(a)
    for m,c in b.items():out[m]=out.get(m,Q(0))+c
    return clean(out)
def pmul(a,b):
    out={}
    for (i,j),c in a.items():
        for (k,l),d in b.items():out[i+k,j+l]=out.get((i+k,j+l),Q(0))+c*d
    return clean(out)
def parsepoly(n):
    if isinstance(n,ast.Constant) and isinstance(n.value,int):return {(0,0):Q(n.value)}
    if isinstance(n,ast.Name) and n.id in ('x','y'):return {(1,0) if n.id=='x' else (0,1):Q(1)}
    if isinstance(n,ast.UnaryOp) and isinstance(n.op,ast.USub):return {m:-c for m,c in parsepoly(n.operand).items()}
    if not isinstance(n,ast.BinOp):raise ValueError('Unexpected polynomial syntax')
    a=parsepoly(n.left)
    if isinstance(n.op,ast.Pow):
        assert isinstance(n.right,ast.Constant) and isinstance(n.right.value,int) and 0<=n.right.value<=4
        out={(0,0):Q(1)}
        for _ in range(n.right.value):out=pmul(out,a)
        return out
    b=parsepoly(n.right)
    if isinstance(n.op,ast.Add):return padd(a,b)
    if isinstance(n.op,ast.Sub):return padd(a,{m:-c for m,c in b.items()})
    if isinstance(n.op,ast.Mult):return pmul(a,b)
    if isinstance(n.op,ast.Div):
        assert set(b)=={(0,0)} and b[(0,0)]
        return clean({m:c/b[(0,0)] for m,c in a.items()})
    raise ValueError('Unexpected polynomial operator')
def pcoeff(v):return dict(zip(((2,0),(1,0),(0,1),(0,0)),map(Q,v)))

def verify_maps(path):
    saved=json.loads(path.read_text())
    assert len(saved['cases'])==4
    for model,row in zip(MODELS,saved['cases']):
        pair,cs,basis,D,Nu,Nv=model
        assert list(pair)==[row['a'],row['b']] and list(cs)==row['minimal_a2_a4_a6']
        dd=parsepoly(ast.parse(row['inverse_denominator'],mode='eval').body)
        assert pcoeff(D)=={m:4*c for m,c in dd.items()}
        for name,coeff in [('inverse_u',Nu),('inverse_v',Nv)]:
            node=ast.parse(row[name],mode='eval').body
            assert isinstance(node,ast.BinOp) and isinstance(node.op,ast.Div)
            nn,den=parsepoly(node.left),parsepoly(node.right)
            assert pmul(pcoeff(coeff),den)==pmul(pcoeff(D),nn)
        assert all(on_curve(tuple(map(Q,P)),cs) for P in basis)
    return hashlib.sha256(path.read_bytes()).hexdigest()

def finite_sieve(model,p):
    pair,cs,basis,D,Nu,Nv=model
    assert prime(p) and p>5 and disc(cs)%p
    roots={}
    for y in range(p):roots.setdefault(y*y%p,[]).append(y)
    points=[None]
    a,b,c=cs
    for x in range(p):
        points.extend((x,y) for y in roots.get((x**3+a*x*x+b*x+c)%p,[]))
    pointset=set(points);n=len(points);qs=factors(n)
    generator=next((P for P in points[1:] if all(mul(n//q,P,cs,p) is not None for q in qs)),None)
    if generator is None:return None  # Noncyclic primes are harmlessly unused.
    table=[];P=None
    for _ in range(n):table.append(P);P=add(P,generator,cs,p)
    assert P is None and len(set(table))==n and set(table)==pointset
    lookup={P:i for i,P in enumerate(table)}
    logs=[lookup[reduce_point(P,p)] for P in basis]
    keep=bytearray(n);exceptional=0
    squares=set(roots)
    for i,P in enumerate(table):
        if P is None or polyval(D,P)%p==0:
            keep[i]=1;exceptional+=1;continue
        inv=pow(polyval(D,P),-1,p)
        keep[i]=int(polyval(Nu,P)*inv%p in squares and polyval(Nv,P)*inv%p in squares)
    return {'p':p,'order':n,'generator':generator,'logs':logs,'keep':keep,
            'table':table,'exceptional_kept':exceptional,
            'table_sha256':canonical_hash(table),'allowed_indices':[i for i in range(n) if keep[i]]}

def sieve_inputs(model,count=20):
    rows=[]
    for p in range(7,2000):
        if prime(p) and disc(model[1])%p:
            row=finite_sieve(model,p)
            if row is not None:
                rows.append(row)
                if len(rows)==count:return rows
    raise RuntimeError('Not enough cyclic good primes')

def decode(v,B):
    L=2*B+1;i,r=divmod(v,L*L);j,k=divmod(r,L)
    return i-B,j-B,k-B

def filter_box(B,sieves):
    L=2*B+1;rows=[];remaining=None
    for row in sieves:
        p,n,logs,keep=row['p'],row['order'],row['logs'],row['keep']
        before=L**3 if remaining is None else len(remaining)
        nxt=[];d1,d2,d3=logs
        if remaining is None:
            for i in range(-B,B+1):
                for j in range(-B,B+1):
                    index=((i+B)*L+j+B)*L
                    r=(i*d1+j*d2-B*d3)%n
                    for k in range(L):
                        if keep[r]:nxt.append(index+k)
                        r=(r+d3)%n
        else:
            for idx in remaining:
                i,j,k=decode(idx,B)
                if keep[(i*d1+j*d2+k*d3)%n]:nxt.append(idx)
        remaining=nxt
        rows.append({k:v for k,v in row.items() if k not in ('table','keep')})
        rows[-1].update({'tested':before,'rejected':before-len(nxt),'retained':len(nxt),
                         'retained_packed_sha256':canonical_hash(nxt)})
        print('sieve',row['p'],'remaining',len(nxt),flush=True)
    return [decode(v,B) for v in remaining],rows

def reconstruct(triple,model):
    P=None
    for n,S in zip(triple,model[2]):P=add(P,mul(n,tuple(map(Q,S)),model[1]),model[1])
    assert on_curve(P,model[1])
    return P

def exact_test(triple,model):
    pair,cs,basis,D,Nu,Nv=model
    P=reconstruct(triple,model)
    row={'coefficients':list(triple),'point':point_record(P),
         'point_sha256':canonical_hash(point_record(P))}
    if P is None:row['status']='elliptic_identity';return row
    row['coordinate_max_bits']=max(abs(z).bit_length() for q in P for z in (q.numerator,q.denominator))
    den=polyval(D,P)
    if den==0:row['status']='inverse_denominator_zero';return row
    U,V=Q(polyval(Nu,P))/den,Q(polyval(Nv,P))/den
    assert pair[0]*(V-1)*(V-9)*(V-25)==pair[1]*(U-1)*(U-9)*(U-25)
    row['inverse_values']=[str(U),str(V)]
    row['inverse_sha256']=canonical_hash([str(U),str(V)])
    if U.denominator!=1 or V.denominator!=1:row['status']='noninteger_inverse';return row
    u,v=int(U),int(V)
    row['U_V']=[str(u),str(v)]
    if u<49 or v<49:row['status']='below_target';return row
    X,Y=isqrt(u),isqrt(v)
    if X*X!=u or Y*Y!=v:row['status']='nonsquare_inverse';return row
    if X%2!=1 or Y%2!=1:row['status']='even_square_root';return row
    n,m=(X-7)//2,(Y-7)//2
    row['n_m']=[str(n),str(m)]
    assert n>=0 and m>=0
    l1,l2=lcm(*range(n+1,n+7)),lcm(*range(m+1,m+7))
    row['lcm_values']=[str(l1),str(l2)]
    row['lcm_equal']=l1==l2
    if Y-X<12:row['status']='gap_below_six';return row
    assert m>=n+6
    row['status']='collision' if l1==l2 else 'lcm_unequal'
    return row

def self_test(model,sieves):
    B=2
    alltriples=[(i,j,k) for i in range(-B,B+1) for j in range(-B,B+1) for k in range(-B,B+1)]
    kept,counts=filter_box(B,sieves[:3])
    brute=[]
    for triple in alltriples:
        P=reconstruct(triple,model);valid=True
        for row in sieves[:3]:
            residue=reduce_point(P,row['p'])
            idx=sum(a*b for a,b in zip(triple,row['logs']))%row['order']
            assert row['table'][idx]==residue
            if not row['keep'][idx]:valid=False
        if valid:brute.append(triple)
    assert kept==brute
    # Known overlapping equal-LCM examples must not be removed by square sieve.
    overlaps={(1,2):(Q(199,9),Q(-2582,27)),(2,5):(Q(5177,49),Q(-351630,343))}
    if model[0] in overlaps:
        P=overlaps[model[0]];assert on_curve(P,model[1])
        for row in sieves:
            idx=row['table'].index(reduce_point(P,row['p']))
            assert row['keep'][idx]
    return {'pair':model[0],'test_bound':B,'triples':len(alltriples),'survivors':len(kept),
            'rational_reduction_comparisons':len(alltriples)*3,'status':'PASS'}

def main():
    if not __debug__:raise SystemExit('Assertions must remain enabled.')
    if hasattr(sys,'set_int_max_str_digits'):sys.set_int_max_str_digits(0)
    ap=argparse.ArgumentParser();ap.add_argument('--output',type=Path,required=True)
    ap.add_argument('--self-test',action='store_true');ap.add_argument('--bound-json',type=Path)
    ap.add_argument('--prime-count',type=int,default=20)
    args=ap.parse_args();assert 1<=args.prime_count<=30
    maps=Path(__file__).resolve().parent.parent/'verify_k6_maps.output.json'
    map_hash=verify_maps(maps)
    if args.self_test:
        assert args.bound_json is None
        data={'mode':'small-box algorithm tests only','map_sha256':map_hash,'curves':[]}
        for model in MODELS:data['curves'].append(self_test(model,sieve_inputs(model,max(3,args.prime_count))))
    else:
        assert args.bound_json is not None,'Production enumeration requires the actual bound certificate.'
        raw=args.bound_json.read_bytes();bounds=json.loads(raw)
        lookup={tuple(r['pair']):r['final_closed_coefficient_bound'] for r in bounds['curves']}
        assert set(lookup)=={m[0] for m in MODELS}
        data={'mode':'complete enumeration of specified closed coefficient boxes; global scope requires bound proof and full-group evidence',
              'map_sha256':map_hash,'bound_certificate_sha256':hashlib.sha256(raw).hexdigest(),
              'bound_certificate_file':args.bound_json.name,'curves':[]}
        for model in MODELS:
            B=lookup[model[0]];assert isinstance(B,int) and 0<=B<=100
            survivors,sieves=filter_box(B,sieve_inputs(model,args.prime_count))
            exact=[exact_test(triple,model) for triple in survivors]
            data['curves'].append({'pair':model[0],'closed_bound':B,'total_triples':(2*B+1)**3,
                                  'sieves':sieves,'exact_survivors':exact,
                                  'exact_status_counts':dict(sorted(Counter(r['status'] for r in exact).items()))})
    data['python_version']=sys.version
    args.output.write_text(json.dumps(data,indent=2)+'\n')
    print('PASS:',data['mode'])

if __name__=='__main__':main()
