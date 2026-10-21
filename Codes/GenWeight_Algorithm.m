

AllSubspaces := function(U,r);

k := Dimension(U);
F := BaseRing(U);
V := VectorSpace(F,k);

B := Matrix(Basis(U));

W := VectorSpace(F,r);
M := KMatrixSpace(F,r,k);
S := Subsets({1..k},r);

sps := [];

for x in S do
y := [a:a in x];
y := Sort(y);

ech := [];
for i in [1..k] do
if i in y then
ech := ech cat [Basis(W)[Index(y,i)]];
else
ech := ech cat [W!0];
end if;
end for;
ech := Transpose(Matrix(ech));

// ech is basically the matrix with elementary basis elements in pivot columns;

bas := [];

pos := {[i,j]:i in [1..r],j in [1..k]|not j in y and i le Max({0} join {s:s in [1..r]|y[s] lt j})}; // conditions cut down unnecessary search
bas := [Basis(M)[(v[1]-1)*k+v[2]]:v in pos]; //For a matrix space magma decides basis by row wise entries
sp := sub<M|bas>;
sps := sps cat [Rowspace((ech+a)*B):a in sp];
end for;

return sps;
end function;



qSystem := function(C,L,F);
k:= Dimension(C);
n:= Degree(C);
B:= Basis(C);
G:= Matrix(L,k,n, [B[i]:i in [1..k]]);
W := Parent(Transpose(G)[1]);
WF,rho := VectorSpace(W,F);
return sub<WF|[rho(Transpose(G)[i]):i in [1..NumberOfColumns(G)]]>;
end function;



GeneralisedWeightsSubcode := function(C,L,F);
wts := [];
for i in [1..Dimension(C)] do //No need for last dimension as we are concerned about non-degenerate>
A := AllSubspaces(C,i);
wts := wts cat [Min({Dimension(qSystem(U,L,F)):U in A})];
end for;
return wts;
end function;



