(* ::Package:: *)

BeginPackage["Deformation6j`"]

(*Needs["CommonDefinitions`"]
Needs["SymbolicQ`"]
Needs["Decomposition`"]*)
(*Needs["DetermineKnots`"]*)

Begin["`FileNames`"]

directory="d:\\Documents\\Rutgers\\Shamil\\6j convolution deformation\\";

FourierData[k_,jMax_,\[CapitalLambda]q_,precision_]:=FileNameJoin[{directory,"FourierData","run k="<>ToString[k]<>" MaxJ="<>ToString[jMax]<>" abs="<>ToString[\[CapitalLambda]q]<>" prec="<>ToString[Round[precision]]<>".txt"}];

SixJAlgebraicFixedK[k_,jtab_]:=FileNameJoin[{directory,"AlgebraicData","Fixed k="<>ToString[k]<>" jtab="<>ToString[jtab]<>".m"}];

TwistsToString[twists0_]:=Module[
	{ans,twists}
,
	twists=twists0/.{Subscript->(ToString[#1]<>"_"<>ToString[#2]&)};
	ans=ToString[twists];
	ans=StringReplace[ans,{"**"->""," "->""}];
	Return[ans];
];

JPretzelFixedK[k_,twists_,creation_]:=FileNameJoin[{directory,"PretzelData","JonesFixedK","Pretzel k="<>ToString[k]<>" twists="<>TwistsToString[twists]<>" "<>TwistsToString[creation]<>".m"}];

SuperJones[twists_,creation_]:=FileNameJoin[{directory,"PretzelData","SuperJones","Pretzel twists="<>TwistsToString[twists]<>" "<>TwistsToString[creation]<>".m"}];

PretzelRepresentatives[knot_]:=FileNameJoin[{directory,"KnotData","PretzelRepresentatives",ToString[knot]<>".m"}];

SuperJonesCandidates[knot_]:=FileNameJoin[{directory,"KnotData","SuperJonesCandidates",ToString[knot]<>".m"}];

End[]

Begin["`Unrefined`"]

basis:=Deformation6j`Verlinde`basis;
algebraicQNum=True;

(*Root of unity we define is expressed as Q=q^(1/2) in terms of conventional notations.
For Unrefined CS this makes all expressions rational in Q.*)
If[algebraicQNum,
	Q[K_]:=Q[K]=Module[
		{poly,x,i,rootnum,n}
	,
		poly=MinimalPolynomial[Exp[(\[Pi] I)/(2K+4)]];
		n=Exponent[poly[x],x];
		(*Selecting proper root*)
		For[rootnum=1,rootnum<=n,rootnum++,
			If[FullSimplify[Root[poly,rootnum]-Exp[\[Pi] I/(2K+4)]]===0,Break[]];
		];
		If[rootnum>n,
			Print["Failed to select proper AlgebraicNumber for Unrefined case, K=",K];
			Return[Indeterminate];
		];
		Return[AlgebraicNumber[Root[poly,rootnum],Table[KroneckerDelta[1,i],{i,0,n-1}]]];
	]
,
	Q[K_]:=Exp[(\[Pi] I)/(2K+4)];
];

QNum[n_,Q_]:=(Q^(2n)-Q^(-2n))/(Q^2-Q^-2);
qNum[n_,q_]:=QNum[n,q^(1/4)];
KNum[n_,K_]:=QNum[n,Q[K]];
QFactorialK[n_,K_]:=\!\(
\*UnderoverscriptBox[\(\[Product]\), \(i = 2\), \(n\)]\(QNum[i, Q[K]]\)\);
\[CapitalNu]:=If[Deformation6j`Main`TriangleQ[##],1,0]&;
\[CapitalDelta][i_,j_,k_,K_]:=If[Deformation6j`Main`TriangleQ[i,j,k,K],
	(*Print["\[CapitalDelta] ",{i,j,k,K}];
	Print[QFactorialK[(i+j+k)/2+1,K]];*)
	Sqrt[(QFactorialK[(i+j-k)/2,K]QFactorialK[(i-j+k)/2,K]QFactorialK[(j+k-i)/2,K])/QFactorialK[(i+j+k)/2+1,K]]
,
	0
];
Prefactor[J_,K_,z_]:=(
	(*Print["Prefactor ",{Subscript[J, 1],Subscript[J, 2],Subscript[J, 3],K,z,QFactorialK[Subscript[J, 1]-z,K]QFactorialK[Subscript[J, 2]-z,K]QFactorialK[Subscript[J, 3]-z,K]}];*)
	((-1)^z QFactorialK[z+1,K])/(QFactorialK[Subscript[J, 1]-z,K]QFactorialK[Subscript[J, 2]-z,K]QFactorialK[Subscript[J, 3]-z,K])
);

Unrefined6j[coloring_,K_]:=Unrefined6j[coloring,K]=Module[
	{j,J,zlow,jedge,Aux,z}
,
	{Subscript[j, 1,2],Subscript[j, 1,3],Subscript[j, 2,3],Subscript[j, 3,4],Subscript[j, 2,4],Subscript[j, 1,4]}=coloring;
	Subscript[J, 1]=(Subscript[j, 1,2]+Subscript[j, 3,4]+Subscript[j, 1,3]+Subscript[j, 2,4])/2;
	Subscript[J, 2]=(Subscript[j, 1,2]+Subscript[j, 3,4]+Subscript[j, 2,3]+Subscript[j, 1,4])/2;
	Subscript[J, 3]=(Subscript[j, 1,3]+Subscript[j, 2,4]+Subscript[j, 2,3]+Subscript[j, 1,4])/2;
	jedge[a_,b_,c_]:=(Subscript[j, a,b]+Subscript[j, a,c]+Subscript[j, b,c])/2;
	Aux[a_,b_,c_,z_]:=(
		(*Print["Aux ",{z,jedge[a,b,c],QFactorialK[z-jedge[a,b,c],K]}];*)
		\[CapitalDelta][Subscript[j, a,b],Subscript[j, a,c],Subscript[j, b,c],K]/QFactorialK[z-jedge[a,b,c],K]
	);
	zlow=Max[jedge[1,2,3],jedge[1,2,4],jedge[1,3,4],jedge[2,3,4]];
	Return[Sum[Prefactor[J,K,z]Aux[1,2,3,z]Aux[1,2,4,z]Aux[1,3,4,z]Aux[2,3,4,z],{z,zlow,Min[Subscript[J, 1],Subscript[J, 2],Subscript[J, 3]]}]];
];

\[CapitalOmega]k[coloring_,K_]:=Unrefined6j[coloring,K]^2;

T[j_,K_]:=Q[K]^(-(j)^2-2j);

Subscript[Af, \[Alpha]_][a_,b_,k_]:=Module[
	{i,j}
,
	{Subscript[i, 1],Subscript[i, 2],Subscript[i, 3]}=Subscript[basis, k][[a]];
	{Subscript[j, 1],Subscript[j, 2],Subscript[j, 3]}=Subscript[basis, k][[b]];
	Return[Refine[1/T[Subscript[j, \[Alpha]],k] KroneckerDelta[Subscript[i, 1],Subscript[j, 1]]KroneckerDelta[Subscript[i, 2],Subscript[j, 2]]KroneckerDelta[Subscript[i, 3],Subscript[j, 3]]]];
];

Subscript[Bf, 1][a_,b_,k_,\[Omega]_]:=Module[
	{i,j}
,
	{Subscript[i, 1],Subscript[i, 2],Subscript[i, 3]}=Subscript[basis, k][[a]];
	{Subscript[j, 1],Subscript[j, 2],Subscript[j, 3]}=Subscript[basis, k][[b]];
	(*Print[{{a,b},KroneckerDelta[Subscript[i, 3],Subscript[j, 3]],KNum[Subscript[i, 1]+1,k],KNum[Subscript[i, 2]+1,k], \!\(
\*UnderoverscriptBox[\(\[Sum]\), \(s = 0\), \(k\)]\((T[s, k]\ KNum[s + 1, k]
\*SubscriptBox[\(\[Omega]\), \(
\*SubscriptBox[\(i\), \(3\)], 
\*SubscriptBox[\(i\), \(2\)], 
\*SubscriptBox[\(i\), \(1\)], s, 
\*SubscriptBox[\(j\), \(1\)], 
\*SubscriptBox[\(j\), \(2\)]\)])\)\)}];*)
	Return[Refine[KroneckerDelta[Subscript[i, 3],Subscript[j, 3]]KNum[Subscript[i, 1]+1,k]KNum[Subscript[i, 2]+1,k] \!\(
\*UnderoverscriptBox[\(\[Sum]\), \(s = 0\), \(k\)]\((T[s, k] KNum[s + 1, k] 
\*SubscriptBox[\(\[Omega]\), \(
\*SubscriptBox[\(i\), \(3\)], 
\*SubscriptBox[\(i\), \(2\)], 
\*SubscriptBox[\(i\), \(1\)], s, 
\*SubscriptBox[\(j\), \(1\)], 
\*SubscriptBox[\(j\), \(2\)]\)])\)\)]];
];
Subscript[Bf, 2][a_,b_,k_,\[Omega]_]:=Module[
	{i,j}
,
	{Subscript[i, 1],Subscript[i, 2],Subscript[i, 3]}=Subscript[basis, k][[a]];
	{Subscript[j, 1],Subscript[j, 2],Subscript[j, 3]}=Subscript[basis, k][[b]];
	Return[Refine[KroneckerDelta[Subscript[i, 1],Subscript[j, 1]]KNum[Subscript[i, 2]+1,k]KNum[Subscript[i, 3]+1,k] \!\(
\*UnderoverscriptBox[\(\[Sum]\), \(s = 0\), \(k\)]\((T[s, k] KNum[s + 1, k] 
\*SubscriptBox[\(\[Omega]\), \(
\*SubscriptBox[\(i\), \(3\)], 
\*SubscriptBox[\(i\), \(2\)], 
\*SubscriptBox[\(i\), \(1\)], 
\*SubscriptBox[\(j\), \(2\)], 
\*SubscriptBox[\(j\), \(3\)], s\)])\)\)]];
];
Subscript[O1F, J_][a_,b_,k_,\[Omega]_]:=Module[
	{i,j}
,
	{Subscript[i, 1],Subscript[i, 2],Subscript[i, 3]}=Subscript[basis, k][[a]];
	{Subscript[j, 1],Subscript[j, 2],Subscript[j, 3]}=Subscript[basis, k][[b]];
	Return[Refine[KroneckerDelta[Subscript[i, 1],Subscript[j, 1]]KNum[Subscript[i, 2]+1,k]KNum[Subscript[i, 3]+1,k]Subscript[\[Omega], Subscript[i, 3],Subscript[i, 2],Subscript[i, 1],Subscript[j, 2],Subscript[j, 3],J]]];
];
Subscript[O2F, J_][a_,b_,k_,\[Omega]_]:=Module[
	{i,j}
,
	{Subscript[i, 1],Subscript[i, 2],Subscript[i, 3]}=Subscript[basis, k][[a]];
	{Subscript[j, 1],Subscript[j, 2],Subscript[j, 3]}=Subscript[basis, k][[b]];
	Return[Refine[KroneckerDelta[Subscript[i, 2],Subscript[j, 2]]KNum[Subscript[i, 1]+1,k]KNum[Subscript[i, 3]+1,k]Subscript[\[Omega], Subscript[i, 3],Subscript[i, 2],Subscript[i, 1],Subscript[j, 1],J,Subscript[j, 3]]]];
];
Subscript[O3F, J_][a_,b_,k_,\[Omega]_]:=Module[
	{i,j}
,
	{Subscript[i, 1],Subscript[i, 2],Subscript[i, 3]}=Subscript[basis, k][[a]];
	{Subscript[j, 1],Subscript[j, 2],Subscript[j, 3]}=Subscript[basis, k][[b]];
	Return[Refine[KroneckerDelta[Subscript[i, 3],Subscript[j, 3]]KNum[Subscript[i, 1]+1,k]KNum[Subscript[i, 2]+1,k]Subscript[\[Omega], Subscript[i, 3],Subscript[i, 2],Subscript[i, 1],J,Subscript[j, 1],Subscript[j, 2]]]];
];

GetMatrix[F_,k_]:=Table[F[a,b],{a,1,Length[Subscript[basis, k]]},{b,1,Length[Subscript[basis, k]]}];

GetMatricesFrom6j[k_,\[Omega]_]:=Module[
	{A,B,\[Alpha],O1,O2,O3}
,
	For[\[Alpha]=1,\[Alpha]<=3,\[Alpha]++,
		Subscript[A, \[Alpha]]=GetMatrix[Subscript[Af, \[Alpha]][##,k]&,k];
		If[debugAll,Print[MatrixForm[Factor[Subscript[A, \[Alpha]]]]]];
	];
	For[\[Alpha]=1,\[Alpha]<=2,\[Alpha]++,
		Subscript[B, \[Alpha]]=GetMatrix[Subscript[Bf, \[Alpha]][##,k,\[Omega]]&,k];
		If[debugAll,Print[MatrixForm[Factor[Subscript[B, \[Alpha]]]]]];
	];
	O1=GetMatrix[Subscript[O1F, 1][##,k,\[Omega]]&,k];
	O2=GetMatrix[Subscript[O2F, 1][##,k,\[Omega]]&,k];
	O3=GetMatrix[Subscript[O3F, 1][##,k,\[Omega]]&,k];
	Return[{Subscript[A, 1],Subscript[A, 2],Subscript[A, 3],Subscript[B, 1],Subscript[B, 2],O1,O2,O3}];
];

DefineUnrefinedRepresentation[Rep_,Oa_,Ob_,A_,B_,K_,SimplifyF_]:=Module[
	{mtab,T,q,t,\[Omega],OAEv,Q0}
,
	T=Q0=Q[K];
	q=Q0^4;
	t=-Q0^(-2K);
	Subscript[\[Omega], j__]:=Subscript[\[Omega], j]=Factor[\[CapitalOmega]k[{j},K]];
	mtab=GetMatricesFrom6j[K,\[Omega]];
	Rep[Subscript[A, 1]]=SparseArray[SimplifyF[mtab[[1]]]];
	Rep[Subscript[A, 2]]=SparseArray[SimplifyF[mtab[[2]]]];
	Rep[Subscript[A, 3]]=SparseArray[SimplifyF[mtab[[3]]]];
	Rep[Subscript[B, 1,2]]=SparseArray[SimplifyF[mtab[[4]]]];
	Rep[Subscript[B, 2,3]]=SparseArray[SimplifyF[mtab[[5]]]];
	Rep[Subscript[Ob, 2,3]]=SparseArray[SimplifyF[mtab[[6]]]];
	Rep[Subscript[Ob, 1,3]]=SparseArray[SimplifyF[mtab[[7]]]];
	Rep[Subscript[Ob, 1,2]]=SparseArray[SimplifyF[mtab[[8]]]];
	OAEv[j_]:=(Q0^(2j) T^2+Q0^(-2j) T^-2);
	Rep[Subscript[Oa, k_]]:=Rep[Subscript[Oa, k]]=SparseArray[Table[{j,j}->SimplifyF[OAEv[Subscript[basis, K][[j,k]]]],{j,1,Length[Subscript[basis, K]]}]];
];

DefineUnrefinedRepresentation[Rep_,Oa_,Ob_,A_,B_,K_]:=DefineUnrefinedRepresentation[Rep,Oa,Ob,A,B,K,FullSimplify];

Subscript[InteriorOFAux, l_][j_,i_,K_]:=Unrefined6j[{l,i[[1]],j[[1]],j[[5]],j[[2]],i[[2]]},K] Unrefined6j[{l,i[[2]],j[[2]],j[[6]],j[[3]],i[[3]]},K] Unrefined6j[{l,i[[3]],j[[3]],j[[7]],j[[4]],i[[4]]},K]Unrefined6j[{l,i[[4]],j[[4]],j[[8]],j[[1]],i[[1]]},K];
Subscript[InteriorOF, l_][j_,i_,K_]:=Subscript[InteriorOFAux, l][j,i,K]/Subscript[InteriorOFAux, 0][j,j,K];

Subscript[TriangleInteriorOFAux, l_][j_,i_,K_]:=Unrefined6j[{l,i[[1]],j[[1]],j[[4]],j[[2]],i[[2]]},K]Unrefined6j[{l,i[[2]],j[[2]],j[[5]],j[[3]],i[[3]]},K]Unrefined6j[{l,i[[3]],j[[3]],j[[6]],j[[1]],i[[1]]},K];
Subscript[TriangleInteriorOF, l_][j_,i_,K_]:=Subscript[TriangleInteriorOFAux, l][j,i,K]/Subscript[TriangleInteriorOFAux, 0][i,i,K];

End[]

Begin["`UnrefinedAnalytic`"]

TriangleQ[i_,j_,k_]:=(i+j>=k&&i+k>=j&&j+k>=i&&Mod[i+j+k,2]==0);

(*Relation to Cherednik variables q=Q^4, t=T^4*)
QNum[n_,Q_]:=(Q^(2n)-Q^(-2n))/(Q^2-Q^-2);
QFactorialS[n_,Q_]:=\!\(
\*UnderoverscriptBox[\(\[Product]\), \(i = 2\), \(n\)]\(QNum[i, Q]\)\);

Cas[j_,Q_]:=Q^(j^2+2j);

\[CapitalDelta][i_,j_,k_,Q_]:=If[TriangleQ[i,j,k],
	Sqrt[(QFactorialS[(i+j-k)/2,Q]QFactorialS[(i-j+k)/2,Q]QFactorialS[(j+k-i)/2,Q])/QFactorialS[(i+j+k)/2+1,Q]]
,
	0
];

Prefactor[J_,Q_,z_]:=(
	((-1)^z QFactorialS[z+1,Q])/(QFactorialS[Subscript[J, 1]-z,Q]QFactorialS[Subscript[J, 2]-z,Q]QFactorialS[Subscript[J, 3]-z,Q])
);

Unrefined6j[coloring_,Q_]:=Unrefined6j[coloring,Q]=Module[
	{j,J,zlow,jedge,Aux,z,K}
,
	{Subscript[j, 1,2],Subscript[j, 1,3],Subscript[j, 2,3],Subscript[j, 3,4],Subscript[j, 2,4],Subscript[j, 1,4]}=coloring;
	Subscript[J, 1]=(Subscript[j, 1,2]+Subscript[j, 3,4]+Subscript[j, 1,3]+Subscript[j, 2,4])/2;
	Subscript[J, 2]=(Subscript[j, 1,2]+Subscript[j, 3,4]+Subscript[j, 2,3]+Subscript[j, 1,4])/2;
	Subscript[J, 3]=(Subscript[j, 1,3]+Subscript[j, 2,4]+Subscript[j, 2,3]+Subscript[j, 1,4])/2;
	jedge[a_,b_,c_]:=(Subscript[j, a,b]+Subscript[j, a,c]+Subscript[j, b,c])/2;
	Aux[a_,b_,c_,z_]:=(
		\[CapitalDelta][Subscript[j, a,b],Subscript[j, a,c],Subscript[j, b,c],Q]/QFactorialS[z-jedge[a,b,c],Q]
	);
	zlow=Max[jedge[1,2,3],jedge[1,2,4],jedge[1,3,4],jedge[2,3,4]];
	Return[Sum[Prefactor[J,Q,z]Aux[1,2,3,z]Aux[1,2,4,z]Aux[1,3,4,z]Aux[2,3,4,z],{z,zlow,Min[Subscript[J, 1],Subscript[J, 2],Subscript[J, 3]]}]];
];

Urefined6j[coloring_,Q_]:=Subscript[Global`\[CapitalOmega], coloring];

Subscript[InteriorOFAux, l_][j_,i_,Q_]:=Unrefined6j[{l,i[[1]],j[[1]],j[[5]],j[[2]],i[[2]]},Q] Unrefined6j[{l,i[[2]],j[[2]],j[[6]],j[[3]],i[[3]]},Q] Unrefined6j[{l,i[[3]],j[[3]],j[[7]],j[[4]],i[[4]]},Q]Unrefined6j[{l,i[[4]],j[[4]],j[[8]],j[[1]],i[[1]]},Q];
Subscript[InteriorOF, l_][j_,i_,Q_]:=Subscript[InteriorOFAux, l][j,i,Q]/Subscript[InteriorOFAux, 0][i,i,Q];

Subscript[TwistedOFAux, l_,m_][j_,i_,Q_]:=((-1)^((j[[5]]-i[[5]]-(j[[6]]-i[[6]]))/2) ((Cas[i[[5]],Q]Cas[j[[6]],Q])/(Cas[j[[5]],Q]Cas[i[[6]],Q]))^(1/2))^m Unrefined6j[{j[[4]],j[[3]],j[[5]],l,i[[5]],i[[3]]},Q]Unrefined6j[{j[[4]],j[[6]],j[[3]],l,i[[3]],i[[6]]},Q]Unrefined6j[{j[[2]],j[[6]],j[[1]],l,i[[1]],i[[6]]},Q]Unrefined6j[{j[[2]],j[[1]],j[[5]],l,i[[5]],i[[1]]},Q]; 
Subscript[TwistedOF, l_,m_][j_,i_,Q_]:=Subscript[TwistedOFAux, l,m][j,i,Q]/Subscript[TwistedOFAux, 0,m][i,i,Q];

Subscript[DoubleOFAux, l_][j_,i_,Q_]:=Unrefined6j[{j[[3]],j[[2]],j[[1]],l,i[[1]],i[[2]]},Q]Unrefined6j[{j[[4]],j[[1]],j[[2]],l,i[[2]],i[[1]]},Q];
Subscript[DoubleOF, l_][j_,i_,Q_]:=Subscript[DoubleOFAux, l][j,i,Q]/Subscript[DoubleOFAux, 0][i,i,Q];

Subscript[TriangleInteriorOFAux, l_][j_,i_,Q_]:=Unrefined6j[{l,i[[1]],j[[1]],j[[4]],j[[2]],i[[2]]},Q]Unrefined6j[{l,i[[2]],j[[2]],j[[5]],j[[3]],i[[3]]},Q]Unrefined6j[{l,i[[3]],j[[3]],j[[6]],j[[1]],i[[1]]},Q];
Subscript[TriangleInteriorOF, l_][j_,i_,Q_]:=Subscript[TriangleInteriorOFAux, l][j,i,Q]/Subscript[TriangleInteriorOFAux, 0][i,i,Q];

End[]

Begin["`Main`"]

debugAll=False;
debug=False;

\[CapitalOmega]:=Global`\[CapitalOmega];

pairs={{3,4},{2,4},{1,4},{1,2},{1,3},{2,3}};
For[\[Alpha]=1,\[Alpha]<=Length[pairs],\[Alpha]++,
		Subscript[num, pairs[[\[Alpha],1]],pairs[[\[Alpha],2]]]=Subscript[num, pairs[[\[Alpha],2]],pairs[[\[Alpha],1]]]=\[Alpha]
];

Subscript[QNum, q_][n_]:=(q^(n/2)-q^(-n/2))/(q^(1/2)-q^(-1/2));
Subscript[QNum, q_,t_][n_,m_]:=(q^(n/2) t^(m/2)-q^(-n/2) t^(-m/2))/(q^(1/2)-q^(-1/2));
Subscript[QFactorialT, q_,t_][n_,m_]:=\!\(
\*UnderoverscriptBox[\(\[Product]\), \(i = 0\), \(n - 1\)]\(
\(\*SubscriptBox[\(QNum\), \(q, t\)]\)[n - m - i, m]\)\);
\[Epsilon]=10^-6;
GeneralPrecisionCut:=CommonDefinitions`RelationsSolve`GeneralPrecisionCut[#,\[Epsilon]]&;
PrecisionCut:=CommonDefinitions`RelationsSolve`PrecisionCut[#1,#2,\[Epsilon]]&;
PrecisionNSolve:=CommonDefinitions`RelationsSolve`PrecisionNSolve[#1,#2,\[Epsilon]]&;

Subscript[M, j_][x1_,x2_,q_,t_]:=Subscript[M, j][x1,x2,q,t]=\!\(
\*UnderoverscriptBox[\(\[Sum]\), \(l = 0\), \(j\)]\((
\*SuperscriptBox[\(x1\), \(j - l\)] 
\*SuperscriptBox[\(x2\), \(l\)] \((
\*UnderoverscriptBox[\(\[Product]\), \(i = 0\), \(l - 1\)]
\*FractionBox[\(
\(\*SubscriptBox[\(QNum\), \(q\)]\)[j - i] 
\(\*SubscriptBox[\(QNum\), \(q, t\)]\)[i, 1]\), \(
\(\*SubscriptBox[\(QNum\), \(q, t\)]\)[j - i - 1, 1] 
\(\*SubscriptBox[\(QNum\), \(q\)]\)[i + 1]\)])\))\)\);
Subscript[g, i_][q_,t_]:=Subscript[g, i][q,t]=\!\(
\*UnderoverscriptBox[\(\[Product]\), \(m = 0\), \(i - 1\)]\((
\*FractionBox[\(
\(\*SubscriptBox[\(QNum\), \(q\)]\)[i - m] 
\(\*SubscriptBox[\(QNum\), \(q, t\)]\)[m, 2]\), \(
\(\*SubscriptBox[\(QNum\), \(q, t\)]\)[i - m - 1, 1] 
\(\*SubscriptBox[\(QNum\), \(q, t\)]\)[m + 1, 1]\)])\)\);
Subscript[T, j_]:=q^(-j^2/4) t^(-j/2);
Subscript[S, OO][q_,k_]:=Subscript[S, OO][q,k]=(2^(-Mod[k,2]/2) q^(1/4 Floor[(k-1)^2/4]))/\!\(
\*UnderoverscriptBox[\(\[Product]\), \(s = 1\), \(Ceiling[
\*FractionBox[\(k - 1\), \(2\)]]\)]\((1 + 
\*SuperscriptBox[\(q\), 
FractionBox[\(k - 2  s\), \(2\)]])\)\);
Subscript[S, i_,j_][q_,t_,k_]:=Subscript[S, i,j][q,t,k]=(Subscript[S, OO][q,k]q^(-i j/2))/Subscript[g, i][q,t] Subscript[M, i][t^(1/2),t^(-1/2),q,t]Subscript[M, j][t^(1/2) q^i,t^(-1/2),q,t]; 
(*Generating admissible colorings*)
TriangleQ[j1_,j2_,j3_,k_]:=(j1+j2>=j3)&&(j1+j3>=j2)&&(j2+j3>=j1)&&(j1+j2+j3)<=2k&&(Mod[j1+j2+j3,2]==0);

TetrahedronQ[i12_,i13_,i23_,i34_,i24_,i14_,k_]:=TriangleQ[i12,i13,i23,k]&&TriangleQ[i23,i34,i24,k]&&TriangleQ[i12,i24,i14,k]&&TriangleQ[i13,i34,i14,k];

Clear[Admissible]
Admissible[k_]:=Admissible[k]=Module[
	{j1,j2,j3,ans={},j}
,
	For[j1=0,j1<=k,j1++,
		For[j2=0,j2<=k,j2++,
			For[j3=0,j3<=k,j3++,
				If[TriangleQ[j1,j2,j3,k],
					AppendTo[ans,{j1,j2,j3}];
				];
			];
		];
	];
	Return[ans];
];

Admissible6[k_]:=Module[
	{i34,i24,i14,i12,i13,i23,ans={}}
,
	For[i12=0,i12<=k,i12++,
		For[i13=0,i13<=k,i13++,
			For[i23=0,i23<=k,i23++,
				For[i34=0,i34<=k,i34++,
					For[i24=0,i24<=k,i24++,
						For[i14=0,i14<=k,i14++,
							If[TetrahedronQ[i12,i13,i23,i34,i24,i14,k],AppendTo[ans,{i12,i13,i23,i34,i24,i14}]]
						];
					];
				];
			];
		];
	];
	Return[ans];
];

Flip[coloring_]:=Permute[coloring,{4,5,6,1,2,3}];

(*Returns the product of S matrix elements*)
SProduct[coloring_,jColoring_,q_,t_,k_]:=\!\(
\*UnderoverscriptBox[\(\[Product]\), \(i = 1\), \(Length[coloring]\)]\(
\(\*SubscriptBox[\(S\), \(jColoring[\([i]\)], coloring[\([i]\)]\)]\)[q, t, k]\)\);

\[CapitalOmega]F[coloring_]:=Subscript@@Prepend[coloring,\[CapitalOmega]];

GenerateLHS[colorings_,k_,jColoring_,q_,t_]:=( 
	Return[\[CapitalOmega]F[jColoring]-Total[Map[SProduct[Flip[#],jColoring,q,t,k]\[CapitalOmega]F[#]&,colorings]]]
);

GetPermutation6[perm4_]:=Module[
	{ans}
,
	ans=Map[Subscript[num, perm4[[#[[1]]]],perm4[[#[[2]]]]]&,pairs];
	Return[ans];
];

Clear[GetColoringRepresentatives];

ColoringRepresentative[coloring_]:=coloring;

GetColoringRepresentatives[k_]:=GetColoringRepresentatives[k]=Module[
	{basis,colorings,permutations4,permutations6,AddVar,vars,coloringrepresentatives}
,
	AddVar[coloring_]:=Module[
		{equivcolorings}
	,
		equivcolorings=Map[Permute[coloring,#]&,permutations6];
		equivcolorings=Sort[equivcolorings];
		If[coloring==equivcolorings[[1]],
			AppendTo[vars,\[CapitalOmega]F[coloring]];
			AppendTo[coloringrepresentatives,coloring]
		,
			\[CapitalOmega]F[coloring]:=\[CapitalOmega]F[equivcolorings[[1]]];
			ColoringRepresentative[coloring]:=equivcolorings[[1]];
		];
	];
	basis=Admissible[k];
	(*Generate array of all colorings*)
	colorings=Admissible6[k];
	If[debugAll,Print["Colorings ",colorings]];
	(*Generate variables*)
	permutations4=Permutations[{1,2,3,4}];
	permutations6=Map[GetPermutation6,permutations4];
	vars={};
	coloringrepresentatives={};
	Map[AddVar,colorings];
	Return[{colorings,coloringrepresentatives}];
];

AbsNorm[tab_]:=Total[Map[Abs,tab]];

Solve6j[k_,q_,t_]:=Module[
	{colorings,coloringrepresentatives,eqs,A,b,sol,i}
,
	{colorings,coloringrepresentatives}=GetColoringRepresentatives[k];
	If[debugAll,Print["coloringrepresentatives ",coloringrepresentatives]];
	eqs=Map[GenerateLHS[colorings,k,#,q,t]&,coloringrepresentatives];
	eqs=Refine[eqs];
	If[debugAll,Print["eqs=",eqs]];
	A=Table[Coefficient[eqs[[i]],\[CapitalOmega]F[coloringrepresentatives[[j]]]],{i,1,Length[eqs]},{j,2,Length[coloringrepresentatives]}];
	If[debugAll,Print["A=",MatrixForm[A]]];
	b=Table[-Coefficient[eqs[[i]],Subscript[\[CapitalOmega], 0,0,0,0,0,0]],{i,1,Length[eqs]}];
	sol=Check[LinearSolve[A,b],Indeterminate];
	If[sol===Indeterminate,
		Print["Failure in LinSolve"];
		Return[Indeterminate];
	];
	If[NumberQ[A[[1,1]]],Print["Relative Error = ",AbsNorm[A . sol-b]/AbsNorm[b]," Abs Norms ",{AbsNorm[A . sol-b],AbsNorm[b]}]];
	Return[sol];
];

Get6jF[k_,q_,t_]:=Module[
	{sol,\[Omega]}
,
	sol=Solve6j[k,q,t];
	If[debug,Print[sol]];
	Subscript[\[Omega], i1_,i2_,i3_,j1_,j2_,j3_]:=Module[
		{tmp,pos}
	,
		If[{i1,i2,i3,j1,j2,j3}=={0,0,0,0,0,0},Return[1]];
		If[debugAll,Print[{i1,i2,i3,j1,j2,j3}]];
		tmp=\[CapitalOmega]F[{i1,i2,i3,j1,j2,j3}];
		tmp[[0]]=List;
		tmp=Delete[tmp,1];
		If[debugAll,Print[tmp]];
		pos=Position[GetColoringRepresentatives[k][[2]],tmp];
		If[Length[pos]==0,Return[0]];
		If[Length[pos]>1,
			Print["Internal Error at Get6jF"];
			Return[Indeterminate]
		];
		pos=pos[[1,1]];
		Return[sol[[pos-1]]];
	];
	Return[\[Omega]];
];

End[]

Begin["`Verlinde`"]

debugAll=False;

ShamilBasis1={{0,0,0},{1,1,0},{1,0,1},{0,1,1}};
ShamilBasis2={{0,0,0},{1,1,0},{2,2,0},{1,0,1},{0,1,1},{2,1,1},{1,2,1},{2,0,2},{1,1,2},{0,2,2}};
Subscript[basis, k_]:=Deformation6j`Main`Admissible[k];
Subscript[basis, 2]:=ShamilBasis2;
Subscript[basis, 1]:=ShamilBasis1;
Subscript[S, i_,j_][q_,t_,k_]:=Subscript[Deformation6j`Main`S, i,j][q,t,k];
Subscript[g, j_][q_,t_]:=Subscript[Deformation6j`Main`g, j][q,t];
dim[i_,q_,t_,k_]:=Subscript[S, 0,i][q,t,k]/Subscript[S, 0,0][q,t,k];

Subscript[T, j_][q_,t_]:=Refine[q^(-j^2/4) t^(-j/2)];
Subscript[Af, \[Alpha]_][a_,b_,q_,t_,k_]:=Module[
	{i,j}
,
	{Subscript[i, 1],Subscript[i, 2],Subscript[i, 3]}=Subscript[basis, k][[a]];
	{Subscript[j, 1],Subscript[j, 2],Subscript[j, 3]}=Subscript[basis, k][[b]];
	Return[Refine[1/Subscript[T, Subscript[j, \[Alpha]]][q,t]KroneckerDelta[Subscript[i, 1],Subscript[j, 1]]KroneckerDelta[Subscript[i, 2],Subscript[j, 2]]KroneckerDelta[Subscript[i, 3],Subscript[j, 3]]]];
];
Subscript[\[CapitalNu], i_,j_,m_][q_,t_,k_]:=\!\(
\*UnderoverscriptBox[\(\[Sum]\), \(l = 0\), \(k\)]
\*FractionBox[\(
\(\*SubscriptBox[\(S\), \(i, l\)]\)[q, t, k] 
\(\*SubscriptBox[\(S\), \(j, l\)]\)[q, t, k] 
\(\*SubscriptBox[\(S\), \(m, l\)]\)[q, t, k]\), \(
\(\*SubscriptBox[\(g\), \(l\)]\)[q, t] 
\(\*SubscriptBox[\(S\), \(0, l\)]\)[q, t, k]\)]\);
Subscript[Bf, 1][a_,b_,q_,t_,k_,\[Omega]_]:=Module[
	{i,j}
,
	{Subscript[i, 1],Subscript[i, 2],Subscript[i, 3]}=Subscript[basis, k][[a]];
	{Subscript[j, 1],Subscript[j, 2],Subscript[j, 3]}=Subscript[basis, k][[b]];
	Return[Refine[KroneckerDelta[Subscript[i, 3],Subscript[j, 3]] dim[Subscript[i, 1],q,t,k]dim[Subscript[i, 2],q,t,k]/Subscript[\[CapitalNu], Subscript[i, 1],Subscript[i, 2],Subscript[i, 3]][q,t,k] \!\(
\*UnderoverscriptBox[\(\[Sum]\), \(s = 0\), \(k\)]\((
\(\*SubscriptBox[\(T\), \(s\)]\)[q, t] dim[s, q, t, k] 
\*SubscriptBox[\(\[Omega]\), \(
\*SubscriptBox[\(i\), \(3\)], 
\*SubscriptBox[\(i\), \(2\)], 
\*SubscriptBox[\(i\), \(1\)], s, 
\*SubscriptBox[\(j\), \(1\)], 
\*SubscriptBox[\(j\), \(2\)]\)])\)\)]];
];
Subscript[Bf, 2][a_,b_,q_,t_,k_,\[Omega]_]:=Module[
	{i,j}
,
	{Subscript[i, 1],Subscript[i, 2],Subscript[i, 3]}=Subscript[basis, k][[a]];
	{Subscript[j, 1],Subscript[j, 2],Subscript[j, 3]}=Subscript[basis, k][[b]];
	Return[Refine[KroneckerDelta[Subscript[i, 1],Subscript[j, 1]] dim[Subscript[i, 2],q,t,k]dim[Subscript[i, 3],q,t,k]/Subscript[\[CapitalNu], Subscript[i, 1],Subscript[i, 2],Subscript[i, 3]][q,t,k] \!\(
\*UnderoverscriptBox[\(\[Sum]\), \(s = 0\), \(k\)]\((
\(\*SubscriptBox[\(T\), \(s\)]\)[q, t] dim[s, q, t, k] 
\*SubscriptBox[\(\[Omega]\), \(
\*SubscriptBox[\(i\), \(3\)], 
\*SubscriptBox[\(i\), \(2\)], 
\*SubscriptBox[\(i\), \(1\)], 
\*SubscriptBox[\(j\), \(2\)], 
\*SubscriptBox[\(j\), \(3\)], s\)])\)\)]];
];
Subscript[O1F, J_][a_,b_,q_,t_,k_,\[Omega]_]:=Module[
	{i,j}
,
	{Subscript[i, 1],Subscript[i, 2],Subscript[i, 3]}=Subscript[basis, k][[a]];
	{Subscript[j, 1],Subscript[j, 2],Subscript[j, 3]}=Subscript[basis, k][[b]];
	Return[Refine[KroneckerDelta[Subscript[i, 1],Subscript[j, 1]]dim[Subscript[i, 2],q,t,k]dim[Subscript[i, 3],q,t,k]Subscript[g, J][q,t]/Subscript[\[CapitalNu], Subscript[i, 1],Subscript[i, 2],Subscript[i, 3]][q,t,k]Subscript[\[Omega], Subscript[i, 3],Subscript[i, 2],Subscript[i, 1],Subscript[j, 2],Subscript[j, 3],J]]];
];
Subscript[O2F, J_][a_,b_,q_,t_,k_,\[Omega]_]:=Module[
	{i,j}
,
	{Subscript[i, 1],Subscript[i, 2],Subscript[i, 3]}=Subscript[basis, k][[a]];
	{Subscript[j, 1],Subscript[j, 2],Subscript[j, 3]}=Subscript[basis, k][[b]];
	Return[Refine[KroneckerDelta[Subscript[i, 2],Subscript[j, 2]]dim[Subscript[i, 1],q,t,k]dim[Subscript[i, 3],q,t,k]Subscript[g, J][q,t]/Subscript[\[CapitalNu], Subscript[i, 1],Subscript[i, 2],Subscript[i, 3]][q,t,k]Subscript[\[Omega], Subscript[i, 3],Subscript[i, 2],Subscript[i, 1],Subscript[j, 1],J,Subscript[j, 3]]]];
];
Subscript[O3F, J_][a_,b_,q_,t_,k_,\[Omega]_]:=Module[
	{i,j}
,
	{Subscript[i, 1],Subscript[i, 2],Subscript[i, 3]}=Subscript[basis, k][[a]];
	{Subscript[j, 1],Subscript[j, 2],Subscript[j, 3]}=Subscript[basis, k][[b]];
	Return[Refine[KroneckerDelta[Subscript[i, 3],Subscript[j, 3]]dim[Subscript[i, 1],q,t,k]dim[Subscript[i, 2],q,t,k]Subscript[g, J][q,t]/Subscript[\[CapitalNu], Subscript[i, 1],Subscript[i, 2],Subscript[i, 3]][q,t,k]Subscript[\[Omega], Subscript[i, 3],Subscript[i, 2],Subscript[i, 1],J,Subscript[j, 1],Subscript[j, 2]]]];
];

GetMatrix[F_,k_]:=Table[F[a,b],{a,1,Length[Subscript[basis, k]]},{b,1,Length[Subscript[basis, k]]}];

GetMatricesFrom6j[q_,t_,k_,\[Omega]_]:=Module[
	{A,B,\[Alpha],O1,O2,O3}
,
	For[\[Alpha]=1,\[Alpha]<=3,\[Alpha]++,
		Subscript[A, \[Alpha]]=GetMatrix[Subscript[Af, \[Alpha]][##,q,t,k]&,k];
		If[debugAll,Print[MatrixForm[Factor[Subscript[A, \[Alpha]]]]]];
	];
	For[\[Alpha]=1,\[Alpha]<=2,\[Alpha]++,
		Subscript[B, \[Alpha]]=GetMatrix[Subscript[Bf, \[Alpha]][##,q,t,k,\[Omega]]&,k];
		If[debugAll,Print[MatrixForm[Factor[Subscript[B, \[Alpha]]]]]];
	];
	Subscript[O1, j_]:=Subscript[O1, j]=GetMatrix[Subscript[O1F, j][##,q,t,k,\[Omega]]&,k];(*Representations for arbitraty j*)
	Subscript[O2, j_]:=Subscript[O2, j]=GetMatrix[Subscript[O2F, j][##,q,t,k,\[Omega]]&,k];
	Subscript[O3, j_]:=Subscript[O3, j]=GetMatrix[Subscript[O3F, j][##,q,t,k,\[Omega]]&,k];
	Return[{Subscript[A, 1],Subscript[A, 2],Subscript[A, 3],Subscript[B, 1],Subscript[B, 2],O1,O2,O3}];
];

GetMatrices[q_,t_,k_]:=Module[
	{\[Omega]}
,
	\[Omega]=Deformation6j`Main`Get6jF[k,q,t];
	Return[GetMatricesFrom6j[q,t,k,\[Omega]]];
];

End[]

Begin["`Fourier`"]

Generate[k_,MaxJ_,\[CapitalLambda]q_,precision_]:=Module[
	{filename,outputstream,j,Q,q,t,sol,coloringrepresentatives}
,
	filename=Deformation6j`FileNames`FourierData[k,MaxJ,\[CapitalLambda]q,precision];
	outputstream=OpenWrite[filename];
	If[outputstream==$Failed,
		Print["Failed to open the file"];
		Abort[];
	];
	coloringrepresentatives=Deformation6j`Main`GetColoringRepresentatives[k][[2]];
	Export[outputstream,{k,Length[coloringrepresentatives],MaxJ},"Table","FieldSeparators"->" "];
	WriteString[outputstream,"\n"];
	Export[outputstream,Delete[coloringrepresentatives,1],"Table","FieldSeparators"->" "];
	WriteString[outputstream,"\n"];
	For[j=0,j<MaxJ,j++,
		Print["Starting with k= ",k,", j= ",j];
		Q=SetPrecision[\[CapitalLambda]q Exp[2 \[Pi] I j/MaxJ],precision];
		q=Q^2;
		t=-Q^-k;
		sol=Deformation6j`Main`Solve6j[k,q,t];
		Export[outputstream,{Q,sol},"Table","FieldSeparators"->" "];
		WriteString[outputstream,"\n"];
	];
	Close[outputstream];
];

RestorePolynomial[ftab_,\[CapitalLambda]q_,q_,powq_]:=Module[
	{ans=0,ctab,numq,j,j0,c}
,
	numq=powq[[2]]-powq[[1]]+1;
	If[\[CapitalLambda]q^numq>1/\[Epsilon],
		Print["Not enough precision"];
		Return[Indeterminate];
	];
	ctab=InverseFourier[ftab];
	ctab=Map[(#/Sqrt[numq])&,ctab];
	If[debug,Print[ctab]];
	For[j=powq[[1]],j<=powq[[2]],j++,
		If[j<0,j0=j,j0=j+1];
		c=ctab[[j0]];
		c=c  \[CapitalLambda]q^(-j);
	If[debugAll,Print[{j,c}]];
		If[Abs[c-Round[c]]>\[Epsilon],
			Print["Failed to restore a polynomial, c=",c,", \[CapitalLambda]q=",\[CapitalLambda]q,", j=",j];
			Return[Indeterminate];
			];
		If[Round[c]!=0,
			ans=ans+Round[c]  q^(j);
		];
	];
	Return[ans];
];

End[]

Begin["`CacheFormulas`"]

debug=False;
\[CapitalOmega]:=Global`\[CapitalOmega];

Subscript[\[CapitalNu], i_,j_,m_][q_,t_,k_]:=Subscript[Deformation6j`Verlinde`\[CapitalNu], i,j,m][q,t,k];
Subscript[S, i_,j_][q_,t_,k_]:=Subscript[Deformation6j`Main`S, i,j][q,t,k];

LoadFormula[]:=( 
	Global`\[CapitalOmega]:=Deformation6j`KnotOperators`\[CapitalOmega]
);

GetCached6jFixedK[k_,jtab_]:=Module[
	{ans,filename,jtabrepr}
,
	If[Position[Deformation6j`Main`GetColoringRepresentatives[k],jtab]==0,
		Print["Inadmissible 6j symbol ",jtab," at level k=",k];
		Return[0];
	];
	jtabrepr=Deformation6j`Main`ColoringRepresentative[jtab];
	filename=Deformation6j`FileNames`SixJAlgebraicFixedK[k,jtabrepr];
	If[FileExistsQ[filename],
		ans=Import[filename]
	,
		Print["No such file to Import, ",filename];
		Return[ans]
	];
	Return[ans];
];

Cache6jFixedK[k_,jtab_,\[Omega]_]:=Module[
	{filename,cached,jtabrepr}
,
	jtabrepr=Deformation6j`Main`\[CapitalOmega]F[jtab];
	jtabrepr[[0]]=List;
	jtabrepr=Delete[jtabrepr,1];
	filename=Deformation6j`FileNames`SixJAlgebraicFixedK[k,jtabrepr];
	If[FileExistsQ[filename],
		Print["File already exists"];
		cached=Import[filename];
		If[Factor[cached-\[Omega]]==0,
			Print["Consistent cache"]
		,
			Print["Failed to compare"];
		];
		Return[];
	];
	Export[filename,\[Omega]];
];

CachePretzel[k_,twists_,creation_,J_]:=Module[
	{filename,cached}
,
	If[J===Indeterminate,
		Print["Indeterminate answer, skip caching"];
		Return[];
	];
	filename=Deformation6j`FileNames`JPretzelFixedK[k,twists,creation];
	If[FileExistsQ[filename],
		cached=Import[filename];
		If[Factor[cached-J]===0,
			Print["Consistent cache for k=",ToString[k]," ttab=",twists]
		,
			Print["Inconsistent cache for k=",ToString[k]," ttab=",twists]
		];
		Return[];
	];
	Export[filename,J];
];

GetCachedJonesFixedK[twists_,creation_,abo_,Q0_,k_]:=Module[
	{poly,filename,a}
,
	filename=Deformation6j`FileNames`JPretzelFixedK[k,twists,creation];
	If[FileExistsQ[filename],
		poly=Import[filename];
		Return[poly];
	];
	poly=Deformation6j`RefinedJones`JonesReconstructFixedK[twists,creation,abo,Q0,k];
	(*poly=Decomposition`Normalized`GenericNormalization[poly,{a,Q0}];*)
	CachePretzel[k,twists,creation,poly];
	Return[poly];
];

AppendPretzelRepresentative[twists_,creation_,knot_]:=Module[
	{filename,stream,representatives}
,
	filename=Deformation6j`FileNames`PretzelRepresentatives[knot];
	If[FileExistsQ[filename],
		representatives=Import[filename];
		If[Position[representatives,{twists,creation}]!={},Return[]];
	];
	stream=OpenAppend[filename];
	If[stream==Null,
		Print["Failed to open the file with Pretzel Representatives"];
		Return[];
	];
	WriteString[stream,ToString[InputForm[{twists,creation}]]<>"\n"];
	Close[stream];
];

AppendSuperJonesCandidate[knot_,P_]:=Module[
	{filename,stream,string,poly,oldans}
,
	If[P===Indeterminate,
		Print["Indeterminate answer stop caching"];
		Return[];
	];
	filename=Deformation6j`FileNames`SuperJonesCandidates[knot];
	If[FileExistsQ[filename],
		oldans=Import[filename];
		If[Position[oldans,P]!={},Return[]];
	];
	stream=OpenAppend[filename];
	If[stream==$Failed,
		Print["Failure in AppendSuperJonesCandidate"];
		Return[];
	];
	WriteString[stream,ToString[InputForm[P]]<>"\n"];
	Close[stream];
];

maxtorus=8;

CacheSuperJonesByKnot[twists_,creation_,P_,q_,t_]:=Module[
	{knots,Jones,Q}
,
	If[P===Indeterminate,
		Print["Indeterminate polynomial stop caching"];
		Return[];
	];
	Jones=P/.{t->Q^2,q->Q^2};
	knots=DetermineKnots`ByJones`GetKnotsList[Jones,Q,maxtorus];
	If[knots=={},Print["No Jones polynomials found corresponding to this pretzel"]];
	Map[AppendPretzelRepresentative[twists,creation,#]&,knots];
	Map[AppendSuperJonesCandidate[#,P]&,knots];
];

CacheSuperJones[twists_,creation_,P_]:=Module[
	{filename,cached}
,
	filename=Deformation6j`FileNames`SuperJones[twists,creation];
	If[P===Indeterminate,
		Print["Indeterminate answer, skip caching"];
		Return[];
	];
	If[FileExistsQ[filename],
		cached=Import[filename];
		If[Factor[cached-P]===0,
			Print["Consistent cache for k=",ToString[k]," ttab=",twists]
		,
			Print["Inconsistent cache for k=",ToString[k]," ttab=",twists]
		];
		Return[];
	];
	Export[filename,P];
];

GetCachedSuperJones[twists_,creation_,abo_,q_,t_]:=Module[
	{filename,P,ans}
,
	filename=Deformation6j`FileNames`SuperJones[twists,creation];
	If[FileExistsQ[filename],
		P=Import[filename];
		Return[P]
	,
		P=Deformation6j`SuperJones`ReconstructSuperJones[twists,creation,abo,q,t];
		ans=Numerator[Factor[P]];
		If[Length[CoefficientRules[Denominator[Factor[P]],{q,t}]]!=1,
			Print["Incorrect form of the SuperJones ",Factor[P]]
		,
			CacheSuperJones[twists,creation,ans];
			CacheSuperJonesByKnot[twists,creation,ans,q,t];
			Return[ans];
		];
	];
];

TorusQ[twists_,creation_]:=(Position[twists,Subscript[Global`a, 2]]=={})&&((Position[twists,Subscript[Global`b, 1]]=={})||(Position[twists,Subscript[Global`b, 2]]=={}));

CacheAllPretzels[maxlength_,creation_,abo_,q_,t_,AvoidQ_]:=Module[
	{rgens,generators,fullbasis,length,basis}
,
	generators=Flatten[Take[abo,2]];
	rgens=Flatten[Take[abo,1]];
	rgens=Delete[rgens,Position[abo[[3]],creation][[1]]];
	fullbasis=NonCommutative`PolynomialIdeals`AssociativeIdealBasis[rgens,1];
	Print[fullbasis];
	For[length=2,length<maxlength,length++,
		Print["Starting with length ",length];
		fullbasis=NonCommutative`PolynomialIdeals`AppendToBasis[fullbasis,{generators},length,maxlength,NonCommutativeMultiply[#2,#1]&];
		fullbasis[[length+1]]=DeleteCases[fullbasis[[length+1]],_?(AvoidQ[#,creation]&)];
		basis=fullbasis[[length+1]];
		Print["Length of basis ",Length[basis]];
		If[debug,Print[basis]];
		DynamicModule[{pos},
			PrintTemporary[Dynamic[pos]];
			For[pos=1,pos<=Length[basis],pos++,
				If[!TorusQ[basis[[pos]],creation],
					Print[Deformation6j`CacheFormulas`GetCachedSuperJones[basis[[pos]],creation,abo,q,t]];
				];
			];
		];
	];
];

End[]

Begin["`KnotOperators`"]

debugAll=True;
SimplifyF:=Factor[Refine[#]]&;

Clear[Orecursive,ORecursivePow]

(*Introducing notations from Main section*)
Subscript[basis, k_]:=Subscript[Deformation6j`Verlinde`basis, k];

BasisNum[k_,i1_,i2_,i3_]:=Module[
	{pos}
,
	pos=Position[Subscript[basis, k],{i1,i2,i3}];
	If[Length[pos]!=1,
		Print["Unexpected basis element ",{i1,i2,i3}];
		Print[Subscript[basis, k]];
		Return[Indeterminate];
	];
	Return[pos[[1,1]]];
];

(*Introducing definitions from the Verlinde section*)
GetMatrix:=Deformation6j`Verlinde`GetMatrix;
\[CapitalNu]:=Deformation6j`Verlinde`\[CapitalNu];
S:=Deformation6j`Verlinde`S;
g:=Deformation6j`Verlinde`g;
O1F:=Deformation6j`Verlinde`O1F;
O2F:=Deformation6j`Verlinde`O2F;
O3F:=Deformation6j`Verlinde`O3F;
dim:=Deformation6j`Verlinde`dim;

Subscript[\[CapitalOmega]0,i_,i1_,m_,j_,j1_][q_,t_,k_]:=KroneckerDelta[i,i1]KroneckerDelta[j,j1] (Subscript[\[CapitalNu], i,j,m][q,t,k](Subscript[S, 0,0][q,t,k])^2)/(Subscript[S, 0,i][q,t,k]Subscript[S, 0,j][q,t,k]);

cp[q_,t_,k_]:=1/(Sqrt[t]) ((1-q)(1+t))/(1-t q);
\[CapitalOmega]1p[n_,v_,u_,q_,t_,k_]:=Subscript[\[CapitalNu], 1,n,n+1][q,t,k]Subscript[\[CapitalNu], n+1,u+1,v][q,t,k]Subscript[\[CapitalNu], 1,u,u+1][q,t,k]Subscript[g, u+1][q,t]/dim[u+1,q,t,k]Subscript[g, n+1][q,t]/dim[n+1,q,t,k](1-t q^((u+n+v)/2+1))(1-q^((u+n-v)/2+1))/(1-q^(u+1))/(1-q^(n+1))cp[q,t,k];

cm[q_,t_,k_]:=((1-q)(1+t))/(1-t q);
\[CapitalOmega]1m[n_,v_,u_,q_,t_,k_]:=Subscript[\[CapitalNu], 1,n,n+1][q,t,k]Subscript[\[CapitalNu], n+1,u-1,v][q,t,k]Subscript[\[CapitalNu], 1,u,u-1][q,t,k]Subscript[g, u-1][q,t]/dim[u,q,t,k]Subscript[g, n+1][q,t]/dim[n+1,q,t,k](1-t q^((v-n+u)/2-1))(1-q^((u-v-n)/2-1))/(1-t q^(u-1))/(1-q^(-n-1))cm[q,t,k];

ColoringPlusQ[coloring_]:=(coloring[[1]]==1)&&(coloring[[3]]-coloring[[2]]==1)&&(coloring[[5]]-coloring[[6]]==1);
ColoringMinusQ[coloring_]:=(coloring[[1]]==1)&&(coloring[[3]]-coloring[[2]]==1)&&(coloring[[6]]-coloring[[5]]==1);

\[CapitalOmega]k[coloring0_,q_,t_,k_]:=Module[
	{coloring,n,v,u,i1,i2,i3,j1,j2,j3,j}
,
	Deformation6j`Main`GetColoringRepresentatives[k];
	If[!Deformation6j`Main`ColoringRepresentative@@Append[coloring0,k],
		Return[0];
	];
	coloring=Deformation6j`Main`ColoringRepresentative[coloring0];
	Switch[coloring[[1]],
	0,
		coloring[[1]]=\[CapitalOmega]0;
		Return[(Subscript@@coloring)[q,t,k]],
	1,
		n=coloring[[2]];
		v=coloring[[4]];
		u=coloring[[6]];
		Switch[coloring,
		_?ColoringPlusQ,
			Return[\[CapitalOmega]1p[n,v,u,q,t,k]],
		_?ColoringMinusQ,
			Return[\[CapitalOmega]1m[n,v,u,q,t,k]],
		_,
			(*Print["Unexpected coloring ",coloring];*)
			Return[0];			
		],
	_,
		{j,i2,j2,i1,j3,i3}=coloring;
		j1=i1;
		If[Deformation6j`Main`TetrahedronQ@@Append[coloring,k],
			Return[Subscript[\[CapitalNu], i1,i2,i3][q,t,k]/(dim[i2,q,t,k]dim[i3,q,t,k]) (Subscript[g, j][q,t])^-1 ORecursive[j,q,t,k][[BasisNum[k,i1,i2,i3],BasisNum[k,j1,j2,j3]]]]
		,
			Return[0]
		];
	];
];
(*The functio below caches the simplified \[Omega]*)
Subscript[(\[Omega]k[q_,t_,k_]), i1_,i2_,i3_,i4_,i5_,i6_]:=Subscript[(\[Omega]k[q,t,k]), i1,i2,i3,i4,i5,i6]=SimplifyF[\[CapitalOmega]k[{i1,i2,i3,i4,i5,i6},q,t,k]];

(*Using explicit formulas (41),(42) for \[CapitalOmega]p and \[CapitalOmega]m as initial conditions for recursion*)
ORecursivePow[pow_,j_,q_,t_,k_,OM_]:=ORecursivePow[pow,j,q,t,k,OM]=Switch[pow,
0,
	Return[IdentityMatrix[Length[Subscript[basis, k]]]],
1,
	ORecursiveGeneral[j,q,t,k,OM],
_?(#>1&),
	Return[ORecursivePow[pow-1,j,q,t,k,OM] . ORecursiveGeneral[j,q,t,k,OM]],
_,
	Print["Unexpected power, ",pow];
	Return[Indeterminate];
];

O1M[q_,t_,k_]:=GetMatrix[Subscript[O1F,1][##,q,t,k,\[Omega]k[q,t,k]]&,k];
O3M[q_,t_,k_]:=GetMatrix[Subscript[O3F,1][##,q,t,k,\[Omega]k[q,t,k]]&,k];

(*Calculating higher knot operators using (66)*)
ORecursiveGeneral[j_,q_,t_,k_,OM_]:=ORecursiveGeneral[j,q,t,k,OM]=Module[
	{ans,i,m,p}
,
	ans=Table[0,{i1,1,Length[Subscript[basis, k]]},{i2,1,Length[Subscript[basis, k]]}];
	Switch[j,
	1,
		Return[OM[q,t,k]],
	_,
		Print["Entering j=",j," q=",q," t=",t," k=",k];
		Qn[n_]:=(q^(n/2)-q^(-n/2))/(q^(1/2)-q^(-1/2));
		QnFactorial[n_]:=\!\(
\*UnderoverscriptBox[\(\[Product]\), \(i = 1\), \(n\)]\(Qn[n]\)\);
		QQn[n_,m_]:=(q^(n/2) t^(m/2)-q^(-n/2) t^(-m/2))/(q^(1/2)-q^(-1/2));
		ans=\!\(
\*UnderoverscriptBox[\(\[Sum]\), \(l = 0\), \(Floor[j/2]\)]\((
\*FractionBox[\(
\*SuperscriptBox[\(q\), \(0  l\)] Qn[j - 2  l + 1]\), \(Qn[j - l + 1]\)] \((
\*UnderoverscriptBox[\(\[Product]\), \(m = 0\), \(l - 1\)]\((
\*FractionBox[\(Qn[j - l + 1 + m] QQn[m - 1, 1]\), \(Qn[m + 1] QQn[j - 1 - m, 1]\)])\))\) \(
\*UnderoverscriptBox[\(\[Sum]\), \(p = 0\), \(Floor[j/2] - l\)]\((
\*FractionBox[\(
\*SuperscriptBox[\((\(-1\))\), \(p\)]\ Factorial[j - 2  l - p]\), \(Factorial[p] Factorial[j - 2  l - 2  p]\)] ORecursivePow[j - 2  l - 2  p, 1, q, t, k, OM])\)\))\)\);
		Return[ans];
	];
];

ORecursive[j_,q_,t_,k_]:=ORecursiveGeneral[j,q,t,k,O1M];
ORecursive3[j_,q_,t_,k_]:=ORecursiveGeneral[j,q,t,k,O3M];

End[]

Begin["`RefinedJones`"]

silent=True;
debug=False;
safeMode=False;
Inv:=Global`Inv;

SimplifyF:=Factor[Refine[#]]&

Subscript[\[CapitalOmega]General[\[Omega]_,k_], j1_,j2_,j3_,j4_,j5_,j6_]:=Module[
	{coloring}
,
	If[Deformation6j`Main`TetrahedronQ[j1,j2,j3,j4,j5,j6,k],
		coloring=Deformation6j`Main`ColoringRepresentative[{j1,j2,j3,j4,j5,j6}];
		(*Print[coloring," ",Subscript@@Prepend[coloring,\[Omega]]];*)
		Return[Subscript@@Prepend[coloring,\[Omega]]]
	,
		Return[0]
	];
];

If[safeMode,Clear[CachedMatrices]];
CachedMatrices[q_,t_,k_]:=CachedMatrices[q,t,k]=Module[
	{A,B,OU,IA,IB,\[CapitalOmega]k,\[Omega]k}
,
	Subscript[\[CapitalOmega]k, j1_,j2_,j3_,j4_,j5_,j6_]:=Deformation6j`KnotOperators`\[CapitalOmega]k[{j1,j2,j3,j4,j5,j6},q,t,k];
	\[Omega]k:=\[CapitalOmega]General[\[CapitalOmega]k,k];
	(*Print["{{0,0,0,0,0,0}} ",Subscript[\[Omega]k, 0,0,0,0,0,0]];*)
	{Subscript[A, 1],Subscript[A, 2],Subscript[A, 3],Subscript[B, 1],Subscript[B, 2],Subscript[OU, 1],Subscript[OU, 2],Subscript[OU, 3]}=SimplifyF[Deformation6j`Verlinde`GetMatricesFrom6j[q,t,k,\[Omega]k]];
	Subscript[IA, 1]=SimplifyF[Inverse[Subscript[A, 1]]];
	Subscript[IA, 2]=SimplifyF[Inverse[Subscript[A, 2]]];
	Subscript[IA, 3]=SimplifyF[Inverse[Subscript[A, 3]]];
	Subscript[IB, 1]=SimplifyF[Inverse[Subscript[B, 1]]];
	Subscript[IB, 2]=SimplifyF[Inverse[Subscript[B, 2]]];
	Return[SimplifyF[{{Subscript[A, 1],Subscript[A, 2],Subscript[A, 3],Subscript[IA, 3],Subscript[IA, 2],Subscript[IA, 1]},{Subscript[B, 1],Subscript[B, 2],Subscript[IB, 2],Subscript[IB, 1]},{Subscript[OU, 1],Subscript[OU, 2],Subscript[OU, 3]}}]];
];

EvaluationMap[word0_,abo_,q_,t_,k_]:=Module[
	{ABO,ZK,evaluationsubs,EvaluationF,A,B,matr,ans,word}
,
	word=NonCommutative`General`BasicExpand[word0];
	If[!silent,Print["word = ",word]];
	ABO=CachedMatrices[q,t,k];
	If[debug,Print["Matrices Loaded"]];
	Subscript[A, 1]=ABO[[1,1]];
	Subscript[A, 2]=ABO[[1,2]];
	Subscript[A, 3]=ABO[[1,3]];
	Subscript[B, 1]=ABO[[2,1]];
	Subscript[B, 2]=ABO[[2,2]];
	evaluationsubs=Table[abo[[i,j]]->ABO[[i,j]],{i,1,Length[abo]},{j,1,Length[abo[[i]]]}];
	evaluationsubs=Flatten[evaluationsubs,1];
	AppendTo[evaluationsubs,NonCommutativeMultiply->Dot];
	AppendTo[evaluationsubs,Inv->Inverse];
	(*Print[evaluationsubs];*)
	EvaluationF[expr_]:=If[expr===1,IdentityMatrix[Length[ABO[[1,1]]]],expr/.evaluationsubs];
	matr=Subscript[A, 1] . Subscript[B, 1] . Subscript[A, 2] . Subscript[B, 2] . Subscript[A, 3] . EvaluationF[word];
	If[debug,Print["Matrix Constructed"]];
	ans=SimplifyF[matr[[1,1]]];
	If[debug,Print["Matrix element simplified"]];
	Return[ans];
];

ZSpecialPoint[twists_,creation_,abo_,q_,t_,k_]:=Module[
	{word}
,
	word=twists**creation**Inv[twists];
	Return[EvaluationMap[word,abo,q,t,k]];
];

ReducedZSpecialPoint[twists_,creation_,abo_,q_,t_,k_]:=ZSpecialPoint[twists,creation,abo,q,t,k]/ZSpecialPoint[1,creation,abo,q,t,k];

primenumstart=10;
primenummax=100;
primenumstep=10;

JonesReconstructFixedK[twists_,creation_,abo_,Q0_,k_]:=Module[
	{primenum,Q,q,t,val,ans1=Indeterminate,ans2,QQ0,QQ}
,
	For[primenum=primenumstart,primenum<=primenummax,primenum+=primenumstep,
		QQ=Prime[primenum];
		Q=QQ^2;
		q=Q^2;
		t=-Q^-k;
		val=ReducedZSpecialPoint[twists,creation,abo,q,t,k];
		If[debug,Print["twists = ",twists," val = ",val]];
		If[ans1===(ans2=CommonDefinitions`Integers`ReconstructRational[val,QQ,Q0^(1/2)]),
			Return[ans1]
		,
			If[debug,Print[{twists,creation}]];
			If[debug,Print[{val,q,ans1,ans2}]];
			ans1=ans2
		];
	];
	Print["Reconstruction of Jones at fixed level function failed"];
	Return[Indeterminate];
];

End[]

Begin["`SuperJones`"]

maxk=7;
Q:=Global`Q;

ReconstructSuperJones[twists_,creation_,abo_,q_,t_]:=Module[
	{k,fixedktab={},ans,tmp,tk,shift,shiftedtab}
,
	For[k=1,k<=maxk,k++,
		tmp=Deformation6j`CacheFormulas`GetCachedJonesFixedK[twists,creation,abo,Q,k];
		tk=-Q^-k;
		AppendTo[fixedktab,{tk,tmp}];
		For[shift=0,shift<=k,shift+=1/2,
			shiftedtab=Map[{#[[1]],#[[1]]^shift #[[2]]}&,fixedktab];
			ans=InterpolatingPolynomial[shiftedtab,t];
			ans=Collect[ans,t,FullSimplify[#,Assumptions->{Q>0}]&];
			If[k>=4&&Coefficient[ans,t,k-1]==0,
				Return[FullSimplify[(t^-shift ans)/.{Q->q^(1/2)},Assumptions->{q>0}]]
			];
		];
	];
	Print["Failed to reconstruct superpolynomial",{twists,creation}];
	Return[Indeterminate];
];

End[]

Begin["`Perturbative`"]

(*Defining Perturbative deformation of 6j symbols*)
DefineGenericLocal6j[rep_,c_]:=(
	rep["vars6j"]={};
	rep["Perturbative6j"][itab_,K_]:=rep["Perturbative6j"][itab,K]=(
		If[Deformation6j`Unrefined`Unrefined6j[itab,K]=!=0,
			If[Position[rep["vars6j"],Subscript[c, itab,K]]=={},
				AppendTo[rep["vars6j"],Subscript[c, itab,K]];
			];
			Deformation6j`Unrefined`Unrefined6j[itab,K]+Subscript[c, itab,K]
		,
			0
		]
	);
	rep["Perturbative6j"][itab_,K_,label_]:=rep["Perturbative6j"][itab,K,label]=(
		If[Deformation6j`Unrefined`Unrefined6j[itab,K]=!=0,
			If[Position[rep["vars6j"],Subscript[c, itab,K,label]]=={},
				AppendTo[rep["vars6j"],Subscript[c, itab,K,label]];
			];
			Deformation6j`Unrefined`Unrefined6j[itab,K]+Subscript[c, itab,K,label]
		,
			0
		]
	);
);

End[]

EndPackage[]


(* ::Input:: *)
(*"Deformation6j`"*)


(* ::Input:: *)
(*"Deformation6j`FileNames`"*)


(* ::Input:: *)
(*"Deformation6j`FileNames`"*)


(* ::Input:: *)
(*"Deformation6j`Main`"*)


(* ::Input:: *)
(*"Deformation6j`Main`"*)


(* ::Input:: *)
(*"Deformation6j`Verlinde`"*)


(* ::Input:: *)
(*"Deformation6j`Verlinde`"*)


(* ::Input:: *)
(*"Deformation6j`Fourier`"*)


(* ::Input:: *)
(*"Deformation6j`Fourier`"*)


(* ::Input:: *)
(*"Deformation6j`CacheFormulas`"*)


(* ::Input:: *)
(*"Deformation6j`CacheFormulas`"*)


(* ::Input:: *)
(*"Deformation6j`KnotOperators`"*)


(* ::Input:: *)
(*"Deformation6j`KnotOperators`"*)
