SetSeed(550); print "VERSION",GetVersion();
SetVerbose("TwoDescent",2); SetVerbose("Selmer",4);
coeffs:=[[0,-1,0,-65,261],[0,-1,0,-408,6912],[0,1,0,-1633,97763],[0,1,0,-1633,32963]];
bases:=[[[5,6],[13,38],[-7,18]],[[12,-60],[-4,92],[78,-666]],[[221/4,3387/8],[14,279],[43,330]],[[23,-90],[17,-102],[-1,186]]];
Qx<t>:=PolynomialRing(Rationals());
for j in [1..4] do
 E:=EllipticCurve(coeffs[j]); print "BEGIN_CASE",j;
 S,a,hints,tovec,FB:=TwoSelmerGroup(E:Raw:=true);
 A:=Domain(a); theta:=A.1;
 print "SELMER_INVARIANTS",Invariants(S);
 print "FACTOR_BASE",FB;
 for i in [1..Ngens(S)] do
  print "SELMER_VECTOR",i,Eltseq(tovec(S.i));
  print "SELMER_REPRESENTATIVE",i,S.i@@a;
 end for;
 imgs:=[a(A!P[1]-theta):P in bases[j]];
 print "BASIS_DESCENT_IMAGES",[Eltseq(z):z in imgs];
 H:=sub<Codomain(a)|imgs>; print "BASIS_IMAGE_ORDER",#H;
 f:=t^3+coeffs[j][2]*t^2+coeffs[j][4]*t+coeffs[j][5];
 K<z>:=NumberField(f); O:=MaximalOrder(K);
 print "MAXIMAL_ORDER_BASIS",[Eltseq(K!v):v in Basis(O)];
 print "FIELD_DISCRIMINANT",Discriminant(O);
 C,cm:=ClassGroup(O); print "CLASS_GROUP",Invariants(C);
 UG,um:=UnitGroup(O); print "UNIT_GROUP",Invariants(UG);
 print "UNIT_GENERATORS",[Eltseq(K!um(UG.i)):i in [1..Ngens(UG)]];
 print "END_CASE",j;
end for;
