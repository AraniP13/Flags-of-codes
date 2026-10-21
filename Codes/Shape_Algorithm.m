

// Make the support dimension equal to the non-zero coordinates and pushes them to the last coordinates 
Squash := function(v,F);

n := Degree(v);
L := BaseField(Parent(v));
V := VectorSpace(F,n);
W,rho := VectorSpace(L,F);

vrho := [rho(v[i]):i in [1..n]];

supp := sub<W|vrho>;
B := Basis(supp);
f1 := #B;
S := VectorSpaceWithBasis(B);

Qp := Transpose(Matrix([Coordinates(S,S!a):a in vrho]));
U := Rowspace(Qp);

Qpp := Matrix(ExtendBasis(U,V)[f1+1..n]);

Q := VerticalJoin(Qpp,Qp);
QL := KMatrixSpace(L,n,n)!Q;
return QL^-1;
end function;



ShapedGen := function(C,L,F,n);
B:= Basis(C);
k:= #B;
GenC:= Matrix(L, k, n, [B[i] : i in [1..#B]]);
GenCE:= EchelonForm(GenC);
vB:= VC!GenCE[k];
QB:= Squash(vB,F);
GenCEB:= GenCE*QB;
for j in [2..k] do
	Gj:= Matrix(L, j, n,[GenCEB[t] : t in [k-j+1..k]]);
	Gj1:= Matrix(L, j-1, n,[GenCEB[t] : t in [k-j+2..k]]);
	fj1:= Dimension(qSystem(Rowspace(Gj1),L,F));
	v1:= VC!Gj[1];
	V1:= VectorSpace(L,n-fj1);
	v:= V1![v1[i]:i in [1..n-fj1]];
	Q1 := Squash(v,F);
	Q:= DiagonalJoin(Q1,IdentityMatrix(L,fj1));
	GenCEB:= GenCEB*Q;
end for;
return GenCEB;
end function;

//Computes the shape of a given code with respect to a specific generator matrix

Shape:= function(C,L,F,n);
G:= ShapedGen(C,L,F,n);
Supp:=[];
for j in [1..k] do
	Gj:= Matrix(L, j, n,[G[t] : t in [k-j+1..k]]);
	fj:= Dimension(qSystem(Rowspace(Gj),L,F));
	Supp:= Supp cat [fj];
end for;
return Supp;
end function;


// Computes optimal lexicographical shape

BestShapeLex:= function(D,L,F);
n:= Degree(D);
GLF:=GL(n,q);
GLL:=GL(n,q^m);
GqL:= sub<GLL|[g:g in Generators(GLF)]>;
BestShape:= Shape(D,L,F,n);
B:= Basis(D);
k:= #B;
GenC:= Matrix(L, k, n, [B[i] : i in [1..#B]]);

for Q in GqL do
	newC:= RowSpace(GenC*Q);
	newBest:= Shape(newC,L,F,n);
	for j in [1..k] do
		if newBest[j] lt BestShape[j] then
			BestShape:= newBest;
			break j;
		end if;
	end for;
end for;

return BestShape;
end function;
