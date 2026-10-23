SetSeed(550);
print "VERSION",GetVersion();
P<U,V,W>:=ProjectiveSpace(Rationals(),2);
for pair in [[1,2],[1,5],[1,10],[2,5]] do
 a:=pair[1]; b:=pair[2];
 C:=Curve(P,a*(V-W)*(V-9*W)*(V-25*W)-b*(U-W)*(U-9*W)*(U-25*W));
 E,f:=EllipticCurve(C,C![1,1,1]); Em,g:=MinimalModel(E); h:=Expand(f*g);
 ok,inv:=IsInvertible(h); assert ok;
 print "PAIR",pair; print "MINIMAL",aInvariants(Em); print "MAP",h; print "INVERSE",inv;
 print "TORSION",TorsionSubgroup(Em);
 G,m:=MordellWeilShaInformation(Em); print "RANK",G; print "GENERATORS",m;
end for;
