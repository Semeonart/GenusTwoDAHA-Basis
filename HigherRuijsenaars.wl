(* ::Package:: *)

BeginPackage["HigherRuijsenaars`"]

Begin["`GenusTwo`"]

SimplifyF:=Factor;
TriangleQ[j1_,j2_,j3_]:=(j1+j2>=j3)&&(j1+j3>=j2)&&(j2+j3>=j1)&&(Mod[j1+j2+j3,2]==0);
(*Relation with Cherednik variables q=Q^4, t=T^4*)
QNum[n_,Q_]:=(Q^(2n)-Q^(-2n))/(Q^2-Q^-2);
QNum[n_,m_,Q_,T_]:=(Q^(2n) T^(2m)-Q^(-2n) T^(-2m))/(Q^2-Q^-2);

(*Wave funtions*)
Subscript[\[CapitalPsi], itab__][x_,Q_,T_]:=Subscript[\[CapitalPsi], itab][x,Table[i,{i,Length[List[itab]]}],Q,T];
(*Defining initial conditions*)
Subscript[p, i_,j_][x_]:=Subscript[x, Min[i,j],Max[i,j]]+Subscript[x, Min[i,j],Max[i,j]]^-1;
Subscript[\[CapitalPsi], jtab__][x_,\[Sigma]_,Q_,T_]:=0/;(!TriangleQ[jtab]);
Subscript[\[CapitalPsi], jtab__][x_,\[Sigma]_,Q_,T_]:=1/;DeleteCases[List[jtab],0]=={};
Subscript[\[CapitalPsi], jtab__][x_,\[Sigma]_,Q_,T_]:=(T^2+T^-2)Subscript[p, \[Sigma][[1]],\[Sigma][[2]]][x]/;(List[jtab][[1]]==1&&List[jtab][[2]]==1&&DeleteCases[List[jtab],0]=={1,1});
(*Defining permutations*)
Subscript[\[CapitalPsi], jtab__][x_,\[Sigma]_,Q_,T_]:=Subscript[\[CapitalPsi], Sequence@@Sort[List[jtab],Greater]][x,\[Sigma][[Reverse[Ordering[List[jtab]]]]],Q,T]/;(!OrderedQ[List[jtab],GreaterEqual]);
(*Defining coefficitients of creation operator*)
Subscript[c, a_,b_][j1_,j2_,j3_,Q_,T_]:=Subscript[c12, a,b][j1,j2,j3,Q,T]=SimplifyF[(a b)(QNum[(a j1+b j2+j3)/2,(a+b+2)/2,Q,T]QNum[(a j1+b j2-j3)/2,(a+b)/2,Q,T]QNum[j1-1,2,Q,T]QNum[j2-1,2,Q,T])/(QNum[j1-1,(a+3)/2,Q,T]QNum[j1,(a+3)/2,Q,T]QNum[j2-1,(b+3)/2,Q,T]QNum[j2,(b+3)/2,Q,T])];
Subscript[c12, a_,b_]:=Subscript[c, a,b];
Subscript[c23, a_,b_][j1_,j2_,j3_,Q_,T_]:=Subscript[c, a,b][j2,j3,j1,Q,T];
Subscript[c13, a_,b_][j1_,j2_,j3_,Q_,T_]:=Subscript[c, a,b][j1,j3,j2,Q,T];
(*Recursive definition for wave function*)
Subscript[\[CapitalPsi], j1_,j2_,j3_][x_,\[Sigma]_,Q_,T_]:=(Subscript[\[CapitalPsi], j1,j2,j3][x,\[Sigma],Q,T]=SimplifyF[1/Subscript[c, 1,1][j1-1,j2-1,j3,Q,T] (Subscript[p, \[Sigma][[1]],\[Sigma][[2]]][x]Subscript[\[CapitalPsi], j1-1,j2-1,j3][x,\[Sigma],Q,T]-Subscript[c, -1,1][j1-1,j2-1,j3,Q,T]Subscript[\[CapitalPsi], j1-2,j2,j3][x,\[Sigma],Q,T]-Subscript[c, 1,-1][j1-1,j2-1,j3,Q,T]Subscript[\[CapitalPsi], j1,j2-2,j3][x,\[Sigma],Q,T]-Subscript[c, -1,-1][j1-1,j2-1,j3,Q,T]Subscript[\[CapitalPsi], j1-2,j2-2,j3][x,\[Sigma],Q,T])])/;(j1>1&&j2>0);

(*Analytic Wave Functions*)
Subscript[\[CapitalKappa][Q_,T_], n1_,n2_,n3_][j1_,j2_,j3_]:=0/;(n1<0||n2<0||n3<0);
Subscript[\[CapitalKappa][Q_,T_], n1_,n2_,n3_][j1_,j2_,j3_]:=Subscript[\[CapitalKappa][Q,T], n2,n1,n3][j2,j1,j3]/;(n2>n1);
Subscript[\[CapitalKappa][Q_,T_], n1_,n2_,n3_][j1_,j2_,j3_]:=Subscript[\[CapitalKappa][Q,T], n1,n3,n2][j1,j3,j2]/;(n3>n2);
Subscript[\[CapitalKappa][Q_,T_], n1_,n2_,n3_][j1_,j2_,j3_]:=(
	(*Print[{n1,n2,n3}];*)
	Subscript[\[CapitalKappa][Q,T], n1,n2,n3][j1,j2,j3]=-((Q^(2 (j2+j3+2 (n2+n3))-2 (j2+j3+2 (2+n2+n3))) (-Q^(8+4 j1)+Q^(4 n1)) (-Q^8+Q^(4 n1) T^4) Subscript[\[CapitalKappa][Q,T], -2+n1,-1+n2,-1+n3][j1,j2,j3])/((-1+Q^(4 n1)) (Q^(4 n1)-Q^(4 j1) T^4)))-1/((-1+Q^(4 n1)) (Q^(4 n1)-Q^(4 j1) T^4)) Q^(4-2 (j2+j3+2 (2+n2+n3))) (Q^(2 (j1+2 (1+j3+n1+2 n2)))-Q^(2 (4+2 j1+j2+j3+2 n2+2 n3))-Q^(2 (j2+j3+2 (2 n1+n2+n3)))+Q^(2 (j1+2 (1+j2+n1+2 n3)))) T^2 Subscript[\[CapitalKappa][Q,T], -1+n1,-1+n2,-1+n3][j1,j2,j3]+(Q^(4+4 n1-2 (j2+j3+2 (2+n2+n3))) (-Q^(2 (j3+2 n2))+Q^(2 (2+j1+j2+2 n3))) (Q^(4+2 j2+4 n3)-Q^(2 (j1+j3+2 n2)) T^4) Subscript[\[CapitalKappa][Q,T], -1+n1,-1+n2,n3][j1,j2,j3])/((-1+Q^(4 n1)) (Q^(4 n1)-Q^(4 j1) T^4))+1/((-1+Q^(4 n1)) (Q^(4 n1)-Q^(4 j1) T^4)) Q^(-2 (j2+j3+2 (2+n2+n3))) (Q^(4+2 (j1+2 (2+j3+n1+2 n2)))-Q^(4+2 (j2+j3+2 (1+n1+n2+n3)))-Q^(4+2 (2+2 j1+j2+j3+2 n1+2 n2+2 n3)) T^4+Q^(4+2 (j1+2 (j2+n1+2 n3))) T^4) Subscript[\[CapitalKappa][Q,T], -1+n1,n2,-1+n3][j1,j2,j3]+1/((-1+Q^(4 n1)) (Q^(4 n1)-Q^(4 j1) T^4)) Q^(-2 (j2+j3+2 (2+n2+n3))) (-Q^(4+2 (j1+2 (1+j3+n1+2 n2))) T^2+Q^(4+2 (4+2 j1+j2+j3+2 n2+2 n3)) T^2+Q^(4+2 (j2+j3+2 (2 n1+n2+n3))) T^2-Q^(4+2 (j1+2 (1+j2+n1+2 n3))) T^2) Subscript[\[CapitalKappa][Q,T], -1+n1,n2,n3][j1,j2,j3]
)/;n1>0;
(*Defining Wave Functions*)
Subscript[d, 1][j1_,j2_,j3_]:=(-j1+j2+j3)/2;
Subscript[d, 2][j1_,j2_,j3_]:=(j1-j2+j3)/2;
Subscript[d, 3][j1_,j2_,j3_]:=(j1+j2-j3)/2;
Subscript[\[CapitalGamma][Q_,T_], k_][n_]:=\!\(
\*UnderoverscriptBox[\(\[Product]\), \(s = 0\), \(n - 1\)]\((1 - 
\*SuperscriptBox[\(T\), \(2  k\)] 
\*SuperscriptBox[\(Q\), \(4  s\)])\)\);
\[CapitalKappa]000[Q_,T_][j1_,j2_,j3_]:=Module[
	{a,b,c,\[Gamma]:=\[CapitalGamma][Q,T]}
,
	a=Subscript[d, 3][j1,j2,j3];
	b=Subscript[d, 2][j1,j2,j3];
	c=Subscript[d, 1][j1,j2,j3];
	Return[T^(-2(a+b+c)) Subscript[\[Gamma], 4][a+b]Subscript[\[Gamma], 4][b+c]Subscript[\[Gamma], 4][a+c]/Subscript[\[Gamma], 4][a+b+c]/Subscript[\[Gamma], 2][a]/Subscript[\[Gamma], 2][b]/Subscript[\[Gamma], 2][c]];
];
Subscript[\[CapitalPsi]\[CapitalKappa][Q_,T_], j1_,j2_,j3_][x12_,x23_,x13_]:=(
	Sum[x12^Subscript[d, 3][j1,j2,j3] x23^Subscript[d, 1][j1,j2,j3] x13^Subscript[d, 2][j1,j2,j3] Subscript[\[CapitalKappa][Q,T], n1,n2,n3][j1,j2,j3](x23/(x12 x13))^n1 (x13/(x12 x23))^n2 (x12/(x13 x23))^n3,{n1,0,j1+j2+j3},{n2,0,j1+j2+j3-n1},{n3,0,j1+j2+j3-n1-n2}]
	/.{Subscript[\[CapitalKappa][Q,T], 0,0,0]->\[CapitalKappa]000[Q,T]}
);

(*Defining q-shift operators*)
\[Delta][x_,\[CapitalLambda]_][expr_]:=expr/.{x->\[CapitalLambda] x};
Subscript[OA, 1][x_,Q_,T_][poly_]:=Sum[i j (((1-T^2 Subscript[x, 2,3] Subscript[x, 1,2]^i Subscript[x, 1,3]^j)(1-T^2 Subscript[x, 2,3]^-1 Subscript[x, 1,2]^i Subscript[x, 1,3]^j))/(T^2 Subscript[x, 1,2]^i Subscript[x, 1,3]^j (Subscript[x, 1,2]-Subscript[x, 1,2]^-1)(Subscript[x, 1,3]-Subscript[x, 1,3]^-1))) \[Delta][Subscript[x, 1,2],Q^(2i)][\[Delta][Subscript[x, 1,3],Q^(2j)][poly]],{i,-1,1,2},{j,-1,1,2}];
Subscript[OA, 2][x_,Q_,T_][poly_]:=Sum[i j (((1-T^2 Subscript[x, 1,3] Subscript[x, 1,2]^i Subscript[x, 2,3]^j)(1-T^2 Subscript[x, 1,3]^-1 Subscript[x, 1,2]^i Subscript[x, 2,3]^j))/(T^2 Subscript[x, 1,2]^i Subscript[x, 2,3]^j (Subscript[x, 1,2]-Subscript[x, 1,2]^-1)(Subscript[x, 2,3]-Subscript[x, 2,3]^-1))) \[Delta][Subscript[x, 1,2],Q^(2i)][\[Delta][Subscript[x, 2,3],Q^(2j)][poly]],{i,-1,1,2},{j,-1,1,2}];
Subscript[OA, 3][x_,Q_,T_][poly_]:=Sum[i j (((1-T^2 Subscript[x, 1,2] Subscript[x, 1,3]^i Subscript[x, 2,3]^j)(1-T^2 Subscript[x, 1,2]^-1 Subscript[x, 1,3]^i Subscript[x, 2,3]^j))/(T^2 Subscript[x, 1,3]^i Subscript[x, 2,3]^j (Subscript[x, 1,3]-Subscript[x, 1,3]^-1)(Subscript[x, 2,3]-Subscript[x, 2,3]^-1))) \[Delta][Subscript[x, 1,3],Q^(2i)][\[Delta][Subscript[x, 2,3],Q^(2j)][poly]],{i,-1,1,2},{j,-1,1,2}];

End[]

Begin["`FiniteDimensionalModules`"]

(*Needs["Deformation6j`"]*)

(*Relation to Cherednik variables q=Q^4, t=TT^2*)
TT[Q_,K_]:=I Q^-K; (*Choice of the sign here is conventional*)
QNumK[n_,m_,Q_,K_]:=(Q^(2n) TT[Q,K]^(m)-Q^(-2n) TT[Q,K]^(-m))/(Q^2-Q^-2);
Subscript[c, a_,b_][j1_,j2_,j3_,Q_,K_]:=Subscript[c, a,b][j1,j2,j3,Q,K]=(a b)(QNumK[(a j1+b j2+j3)/2,(a+b+2)/2,Q,K]QNumK[(a j1+b j2-j3)/2,(a+b)/2,Q,K]QNumK[j1-1,2,Q,K]QNumK[j2-1,2,Q,K])/(QNumK[j1-1,(a+3)/2,Q,K]QNumK[j1,(a+3)/2,Q,K]QNumK[j2-1,(b+3)/2,Q,K]QNumK[j2,(b+3)/2,Q,K]);

Ob12[jj1_,jj2_,Q_,K_]:=Module[
	{a,b}
,
	If[jj1[[3]]!=jj2[[3]],Return[0]];
	a=jj1[[1]]-jj2[[1]];
	b=jj1[[2]]-jj2[[2]];
	If[Abs[a]+Abs[b]!=2,Return[0]];
	Return[Subscript[c, a,b][jj2[[1]],jj2[[2]],jj2[[3]],Q,K]];
];

Ob23[jj1_,jj2_,Q_,K_]:=Module[
	{a,b}
,
	If[jj1[[1]]!=jj2[[1]],Return[0]];
	a=jj1[[2]]-jj2[[2]];
	b=jj1[[3]]-jj2[[3]];
	If[Abs[a]+Abs[b]!=2,Return[0]];
	Return[Subscript[c, a,b][jj2[[2]],jj2[[3]],jj2[[1]],Q,K]];
];

Ob13[jj1_,jj2_,Q_,K_]:=Module[
	{a,b}
,
	If[jj1[[2]]!=jj2[[2]],Return[0]];
	a=jj1[[1]]-jj2[[1]];
	b=jj1[[3]]-jj2[[3]];
	If[Abs[a]+Abs[b]!=2,Return[0]];
	Return[Subscript[c, a,b][jj2[[1]],jj2[[3]],jj2[[2]],Q,K]];
];

GetO[Oa_,Ob_,Rep_,Q_,K_,SimplifyF_]:=Module[
	{Num,ob12rules,i,ob23rules,ob13rules,\[CapitalLambda],m,j,basis,AdmissibleQ}
,
	basis=Subscript[Deformation6j`Verlinde`basis, K];
	AdmissibleQ[jtab__]:=Deformation6j`Main`TriangleQ[jtab,K];
	Num[jtab_]:=Num[jtab]=Module[
		{pos}
	,
		pos=Position[Subscript[basis, K],jtab];
		If[Length[pos]!=1,
			Print["Unexpected basis labels ",jtab,", pos=",pos];
			Return[Indeterminate];
		];
		Return[pos[[1,2]]];
	];
	(*Defining Rep[Subscript[Ob, 1,2]]*)
	ob12rules=Table[
		If[AdmissibleQ@@(basis[[i]]+{a,b,0}),
			{Num[basis[[i]]+{a,b,0}],Num[basis[[i]]]}->Ob12[basis[[i]]+{a,b,0},basis[[i]],Q,K]
		,
			{}
		]
	,
		{i,1,Length[basis]},{a,-1,1,2},{b,-1,1,2}
	];
	ob12rules=Flatten[ob12rules];
	ob12rules=ParallelMap[SimplifyF,ob12rules];
	Rep[Subscript[Ob, 1,2]]=SparseArray[ob12rules];
	(*Defining Rep[Subscript[Ob, 2,3]]*)
	ob23rules=Table[
		If[AdmissibleQ@@(basis[[i]]+{0,a,b}),
			{Num[basis[[i]]+{0,a,b}],Num[basis[[i]]]}->Ob23[basis[[i]]+{0,a,b},basis[[i]],Q,K]
		,
			{}
		]
	,
		{i,1,Length[basis]},{a,-1,1,2},{b,-1,1,2}
	];
	ob23rules=Flatten[ob23rules];
	ob23rules=ParallelMap[SimplifyF,ob23rules];
	Rep[Subscript[Ob, 2,3]]=SparseArray[ob23rules];
	(*Defining Rep[Subscript[Ob, 1,3]]*)
	ob13rules=Table[
		If[AdmissibleQ@@(basis[[i]]+{a,0,b}),
			{Num[basis[[i]]+{a,0,b}],Num[basis[[i]]]}->Ob13[basis[[i]]+{a,0,b},basis[[i]],Q,K]
		,
			{}
		]	
	,
		{i,1,Length[basis]},{a,-1,1,2},{b,-1,1,2}
	];
	ob13rules=Flatten[ob13rules];
	ob13rules=ParallelMap[SimplifyF,ob13rules];
	Rep[Subscript[Ob, 1,3]]=SparseArray[ob13rules];
	(*Defining Rep[Oa]*)
	\[CapitalLambda][j_]:=Q^(2j) TT[Q,K]+Q^(-2j) (TT[Q,K])^-1;
	For[j=1,j<=3,j++,
		With[{k=j},
			Rep[Subscript[Oa, k]]=SparseArray[Table[{i,i}->\[CapitalLambda][basis[[i,k]]],{i,1,Length[basis]}]];
		];
	];
];

GetO[Oa_,Ob_,Rep_,Q_,K_]:=GetO[Oa,Ob,Rep,Q,K,Factor];

(*Dehn Tsists*)

QNum:=HigherRuijsenaars`GenusTwo`QNum;

Subscript[g, i_][Q_,K_]:=Subscript[g, i][Q,K]=\!\(
\*UnderoverscriptBox[\(\[Product]\), \(m = 0\), \(i - 1\)]\((
\*FractionBox[\(QNum[i - m, Q] QNumK[m, 2, Q, K]\), \(QNumK[i - m - 1, 1, Q, K] QNumK[m + 1, 1, Q, K]\)])\)\);

Pow[M_,k_]:=Pow[M,k]=Switch[k,
0,
	Return[SparseArray[Table[{i,i}->1,{i,1,Length[M]}]]],
1,
	Return[M],
_?(#>1&),
	Return[Pow[M,k-1].M],
_,
	Print["Unexpected Power k=",k];
	Return[Indeterminate]
];

Macdonald[M_,j_,Q_,K_]:=Macdonald[M,j]=Module[
	{ans,i,m,p}
,
	Switch[j,
	0,
		Return[Pow[M,0]],
	1,
		Return[M],
	_,
		If[debug,Print["Entering j=",j," Q=",Q," K=",K]];
		ans=\!\(
\*UnderoverscriptBox[\(\[Sum]\), \(l = 0\), \(Floor[j/2]\)]\((
\*FractionBox[\(QNum[j - 2  l + 1, Q]\), \(QNum[j - l + 1, Q]\)] \((
\*UnderoverscriptBox[\(\[Product]\), \(m = 0\), \(l - 1\)]\((
\*FractionBox[\(QNum[j - l + 1 + m, Q] QNumK[m - 1, 1, Q, K]\), \(QNum[m + 1, Q] QNumK[j - 1 - m, 1, Q, K]\)])\))\) \(
\*UnderoverscriptBox[\(\[Sum]\), \(p = 0\), \(Floor[j/2] - l\)]\((
\*FractionBox[\(
\*SuperscriptBox[\((\(-1\))\), \(p\)]\ Factorial[j - 2  l - p]\), \(Factorial[p] Factorial[j - 2  l - 2  p]\)] Pow[M, j - 2  l - 2  p])\)\))\)\);
		Return[ans];
	];
];

(*Defining SL2 Macdonald Polynomials*)
Subscript[P, j_][p_,Q_,T_]:=0/;j<0;
Subscript[P, 0][p_,Q_,T_]:=1;
Subscript[P, 1][p_,Q_,T_]:=p;
Subscript[P, j_][p_,Q_,K_]:=(Factor[p Subscript[P, j-1][p,Q,K]-(QNumK[j-2,2,Q,K]QNum[j-1,Q])/(QNumK[j-2,1,Q,K]QNumK[j-1,1,Q,K]) Subscript[P, j-2][p,Q,K]])/;j>=2;

(*Defining Dehn Twist by knot operator*)
Dehn[M_,Q_,K_]:=Sum[Q^(-j^2) TT[Q,K]^-j (Subscript[P, j][TT[Q,K]+TT[Q,K]^-1,Q,K] Macdonald[M,j,Q,K])/Subscript[g, j][Q,K],{j,0,K}];

GetMCGRep[A_,B_,Oa_,Ob_,Rep_,Q_,K_,SimplifyF_]:=(
	GetO[Oa,Ob,Rep,Q,K];
	Rep[Subscript[A, i_]]:=Rep[Subscript[A, i]]=SparseArray[ParallelMap[SimplifyF,ArrayRules[Dehn[Rep[Subscript[Oa, i]],Q,K]]]];
	Rep[Subscript[B, i_,j_]]:=Rep[Subscript[B, i,j]]=SparseArray[ParallelMap[SimplifyF,ArrayRules[Dehn[Rep[Subscript[Ob, i,j]],Q,K]]]];
);

GetMCGRep[A_,B_,Oa_,Ob_,Rep_,Q_,K_]:=GetMCGRep[A,B,Oa,Ob,Rep,Q,K,Factor];

End[]

EndPackage[]
