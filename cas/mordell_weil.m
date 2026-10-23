SetSeed(550); print "VERSION",GetVersion();
for coeff in [[0,-1,0,-65,261],[0,-1,0,-408,6912],[0,1,0,-1633,97763],[0,1,0,-1633,32963]] do
 E:=EllipticCurve(coeff); print "MODEL",coeff;
 G,m,rankproved,fullproved:=MordellWeilGroup(E);
 print "GROUP",G; print "RANKPROVED",rankproved; print "FULLPROVED",fullproved;
 print "BASIS",[m(G.i):i in [1..Ngens(G)]];
end for;
