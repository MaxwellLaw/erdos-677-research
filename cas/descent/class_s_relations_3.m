SetSeed(550); print "VERSION",GetVersion();
Qx<t>:=PolynomialRing(Rationals());
coeffs:=[[-1,-65,261],[-1,-408,6912],[1,-1633,97763],[1,-1633,32963]];
bounds:=[33,77,542,374]; oddpowers:=[1,27,3,3];
for j in [3] do
  a:=coeffs[j]; K<z>:=NumberField(t^3+a[1]*t^2+a[2]*t+a[3]); O:=MaximalOrder(K);
  C,cm:=ClassGroup(O : Proof:="Full");
  print "BEGIN_CASE",j;
  print "ORDER_BASIS",[Eltseq(K!v):v in Basis(O)];
  print "MINKOWSKI_UPPER",bounds[j];
  Ps:=[Parent(ideal<O|1>)|]; rationals:=[Integers()|];
  for p in PrimesUpTo(bounds[j]) do
    ds:=Decomposition(O,p);
    print "DECOMP",p,#ds;
    for d in ds do
      P:=d[1]; Append(~Ps,P); Append(~rationals,p);
      print "IDEAL",#Ps,p,d[2],Norm(P),[Eltseq(v):v in Basis(P)];
    end for;
  end for;
  h:=oddpowers[j]; SI:=[i:i in [1..#Ps]|rationals[i] in (j eq 1 select [2,3] else [2,3,5])];
  s0:=0;
  for i in SI do
    if h*(Ps[i]@@cm) ne C!0 then s0:=i;break;end if;
  end for;
  if s0 eq 0 and j ne 2 then
    for i in [1..#Ps] do
      if h*(Ps[i]@@cm) ne C!0 then s0:=i;break;end if;
    end for;
  end if;
  print "S_IDEALS",SI; print "ANCHOR",s0;
  for i in [1..#Ps] do
    if Norm(Ps[i]) gt bounds[j] then continue;end if;
    b:= h*(Ps[i]@@cm) eq C!0 select 0 else 1;
    I:=Ps[i]^h;
    if b eq 1 then
      assert s0 ne 0 and h*(Ps[i]@@cm)+h*(Ps[s0]@@cm) eq C!0;
      I*:=Ps[s0]^h;
    end if;
    ok,g:=IsPrincipal(I);assert ok;
    print "RELATION",i,h,b,[Rationals()!c:c in Eltseq(O!g)];
  end for;
  print "END_CASE",j;
end for;
