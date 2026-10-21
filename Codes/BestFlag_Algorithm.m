
// Generates all subspaces of given dimension r of U  
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

// Generates subspaces of U a given dimension t containing a given smaller subspace U0

AllSubspacesThrough := function(U,U0,t);
k := Dimension(U);
k0 := Dimension(U0);
B := ExtendBasis(U0,U);
V := Generic(U);
U1 := sub<V|B[k0+1..k]>;
return {sub<V|U0,a>:a in AllSubspaces(U1,t-k0)};
end function;

// Generates a generator matrix of space C, over extension field L of F and compute the F-column span

qSystem := function(C,L,F);
k:= Dimension(C);
n:= Degree(C);
B:= Basis(C);
G:= Matrix(L,k,n, [B[i]:i in [1..k]]);
W := Parent(Transpose(G)[1]);
WF,rho := VectorSpace(W,F);
return sub<WF|[rho(Transpose(G)[i]):i in [1..NumberOfColumns(G)]]>;
end function;


// Compute the optimal complete flags of subspaces of D1 (n-dimensional space over extension field L over F) 
// Optimality with respect to dimension of the q-system of the Flag elements in lexicographical order

BestFlagF := function(D1,L,F,n);
k2:=Dimension(D1);
VC := VectorSpace(L,n);
Zero:= sub<VC|0>;
BestFlags:={<Zero>};
allBestSupp:=[];
dim:=0;
qcount:=[];

while dim lt k2 do
	BestSupp:=n;
	newBest:={};
		bestbig:= {f[#f]:f in BestFlags};
		A:= &join {AllSubspacesThrough(D1,s,dim+1): s in bestbig};
		ctt:=0;
		for s in A do
			t1:= Dimension(qSystem(s,L,F));
			ctt:= ctt+1;
			if t1 lt BestSupp then
				BestSupp:= t1;
				newBest:= {s};
			else 
				if t1 eq BestSupp then
					newBest:= newBest join {s};
				end if;
			end if;
		end for;
	bestchain:= {f cat <s>:f in BestFlags, s in newBest|f[#f] subset s};
	BestFlags:= bestchain;
	allBestSupp:= allBestSupp cat [BestSupp];
	dim:= dim +1;
	qcount:= qcount cat [ctt];
end while;
//return BestFlags; //uncomment this line to get the list of optimal Flags of the code
return allBestSupp,qcount;
end function;
