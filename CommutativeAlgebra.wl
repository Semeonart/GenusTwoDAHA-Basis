(* ::Package:: *)

BeginPackage["CommutativeAlgebra`"]

Begin["`Graded`"]

silent=False;

DefineFiltration[commalg_,gradedflag_]:=Module[
	{DefineZeroDeg,DefineInadmissibleGrading}
,	
	DefineZeroDeg[]:=(
		commalg["ZeroDeg"]=If[NumberQ[commalg["Deg"][commalg["generators"][[1]]]],
			0
		,
			Map[0&,commalg["Deg"][commalg["generators"][[1]]]]
		];
	);
	DefineInadmissibleGrading[]:=(
		If[NumberQ[commalg["ZeroDeg"]],
			commalg["InadmissibleGradingQ"]:=(#<0)&
		,
			commalg["InadmissibleGradingQ"][degtab_]:=Or@@Flatten[Map[#<0&,degtab]];
		];
	);
	If[$VersionNumber>=12.2,
		If[!ValueQ[commalg["ZeroDeg"],Method->"TrialEvaluation"],DefineZeroDeg[]];
		If[!ValueQ[commalg["InadmissibleGradingQ"],Method->"TrialEvaluation"],DefineInadmissibleGrading[]];
	,
		If[!ValueQ[commalg["ZeroDeg"]],DefineZeroDeg[]];
		If[!ValueQ[commalg["InadmissibleGradingQ"]],DefineInadmissibleGrading[]];
	];
	commalg["Deg"][x_?(NumberQ)]:=commalg["ZeroDeg"];
	commalg["Deg"][x_Plus]:=Module[
		{xtab=x,ans}
	,
		xtab[[0]]=List;
		ans=DeleteDuplicates[Map[commalg["Deg"],xtab]];
		If[gradedflag&&(Length[ans]!=1),
			If[!silent,Print["Polynomial is not homogeneous ",x]];
			Return[Indeterminate];
		];
		ans=Sort[ans,Greater];
		Return[ans[[1]]];
	];
	commalg["Deg"][x_Times]:=Module[
		{xtab=x}
	,
		xtab[[0]]=List;
		Return[Plus@@Map[commalg["Deg"],xtab]];
	];
	commalg["Deg"][x_Power]:=x[[2]]commalg["Deg"][x[[1]]];
];

DefineFiltration[commalg_]:=DefineFiltration[commalg,False];

DefineGrading[commalg_]:=(
	DefineFiltration[commalg,True];
	commalg["GetHomogeneous"][poly_]:=Module[
		{expr=Expand[poly],tab,ans={},degtab={},pos,HandleTerm}
	,
		HandleTerm[monomial_]:=(
			pos=Position[degtab,commalg["Deg"][monomial]];
			Switch[Length[pos],
			0,
				AppendTo[ans,monomial];
				AppendTo[degtab,commalg["Deg"][monomial]],
			1,
				ans[[pos[[1,1]]]]+=monomial,
			_,
				Print["Unexpected Position List in GetHomogeneous, pos=",pos];
				Return[Indeterminate];
			];
		);
		Switch[expr,
		_Plus,
			expr[[0]]=List;
			Map[HandleTerm,expr];
			Return[ans],
		_, 
			Return[{expr}]
		];
	];
	commalg["Deg"][poly_,"Top"]:=Module[
		{homdec}
	,
		homdec=commalg["GetHomogeneous"][poly];
		Return[Max@@Map[commalg["Deg"],homdec,1]];
	];
);

PosQ[xtab_]:=And@@Map[#>=0&,xtab]; (*Auxiliary function for StrictGradedBasis and StrictFilteredSpan*)

(*Defining graded basis for finitenly generated commutative algebra with generators of strictly positive degree*)
DefineStrictGradedSpan[commalg_,SimplifyF_]:=Module[
	{i,j}
,
	(*Defining basis recursively*)
	commalg["gspan"][deg_List]:=commalg["gspan"][deg]=Module[
		{ans={},k,lbasis}
	,
		If[DeleteCases[deg,0]=={},Return[{1}]];
		If[DeleteDuplicates[Map[NumberQ,deg]]=!={True},
			Print["Unexpected input in graded basis ",deg];
			Return[Indeterminate];
		];
		If[!PosQ[deg],Return[{}]];
		For[k=1,k<=Length[commalg["generators"]],k++,
			lbasis=commalg["gspan"][deg-commalg["Deg"][commalg["generators"][[k]]]];
			ans=Join[ans,Map[# commalg["generators"][[k]]&,lbasis]];
		];
		Return[DeleteDuplicates[SimplifyF[ans]]];
	];
];

DefineStrictGradedSpan[commalg_]:=DefineStrictGradedSpan[commalg,Factor];

(*Defining filtered span for finitenly generated commutative algebra with generators of strictly positive degree*)
DefineStrictFilteredSpan[commalg_,SimplifyF_]:=Module[
	{i,j}
,
	(*Defining basis recursively*)
	commalg["fspan"][deg_List]:=commalg["fspan"][deg]=Module[
		{ans={},k,lbasis,deglower}
	,
		If[DeleteCases[deg,0]=={},Return[{1}]];
		If[DeleteDuplicates[Map[NumberQ,deg]]=!={True},
			Print["Unexpected input in filtered span ",deg];
			Return[Indeterminate];
		];
		If[!PosQ[deg],Return[{}]];
		For[k=1,k<=Length[deg],k++,
			If[deg[[k]]>0,
				deglower=deg;
				deglower[[k]]--;
				ans=Join[ans,commalg["fspan"][deglower]];
			];
		];
		For[k=1,k<=Length[commalg["generators"]],k++,
			lbasis=commalg["fspan"][deg-commalg["Deg"][commalg["generators"][[k]]]];
			ans=Join[ans,Map[# commalg["generators"][[k]]&,lbasis]];
		];
		Return[DeleteDuplicates[SimplifyF[ans]]];
	];
	commalg["fspan"][deg_?NumberQ]:=commalg["fspan"][{deg}];
];

DefineStrictFilteredSpan[commalg_]:=DefineStrictFilteredSpan[commalg,Factor];

End[]

Begin["`PolynomialAlgebra`"]

silent=False;
debug=False;
debugAll=False;

Define[polynomialalg_]:=(
	CommutativeAlgebra`Graded`DefineGrading[polynomialalg];
	CommutativeAlgebra`Graded`DefineStrictGradedSpan[polynomialalg];
	CommutativeAlgebra`Graded`DefineStrictFilteredSpan[polynomialalg];
);

(*polynomialalg should be a graded free commutative algebra, \[Rho] is an injection to polynomial algebra*)
DefineStrictGradedAlgebra[commalg_,polynomialalg_,\[Rho]_]:=Module[
	{k,vars=polynomialalg["generators"]}
,
	commalg["GeneratorQ"][x_]:=Position[commalg["generators"],x,1]!={};
	commalg["\[Rho]"]=\[Rho];
	commalg["polynomialalg"]=polynomialalg;
	For[k=1,k<=Length[commalg["generators"]],k++,
		commalg["Deg"][commalg["generators"][[k]]]=polynomialalg["Deg"][\[Rho][commalg["generators"][[k]]]];
	];
	CommutativeAlgebra`Graded`DefineGrading[commalg];
	CommutativeAlgebra`Graded`DefineStrictGradedSpan[commalg];
	(*Defining coefficient rules for basis elements*)
	commalg["spanrules"][deg_]:=commalg["spanrules"][deg]=Module[
		{rulestab,maxpow=Table[1,Length[vars]],i,base,sparserules,j}
	,
		rulestab=Table[CoefficientRules[(Times@@vars)\[Rho][commalg["gspan"][deg][[i]]],vars],{i,1,Length[commalg["gspan"][deg]]}];
		For[i=1,i<=Length[rulestab],i++,
			For[j=1,j<=Length[rulestab[[i]]],j++,
				maxpow=Table[Max[maxpow[[k]],rulestab[[i,j,1,k]]],{k,1,Length[vars]}];
			];
		];
		commalg["baseNum"][deg]=maxpow;
		sparserules=Table[SparseArray[rulestab[[i]],maxpow],{i,1,Length[rulestab]}];
		Return[sparserules];
	];
	(*Defining decomposition of homogeneous monomials*)
	commalg["DecomposeHomogeneous"][poly0_]:=Module[
		{deg,spanrules,rules,diff,eqs,sol,poly,maxpow=Table[1,Length[vars]],j,ans,c}
	,
		poly=Factor[poly0];
		If[poly===0,Return[0]];
		deg=polynomialalg["Deg"][poly];
		(*Finding if there are any basis elements in such degree*)
		spanrules=commalg["spanrules"][deg];
		If[Length[spanrules]==0,
			If[!silent,Print["No elements in such degre, ",deg]];
			Return[Indeterminate];
		];
		(*Finding if maximum powers of generators in basis elements are large enough*)
		rules=CoefficientRules[(Times@@vars)poly,vars];
		For[j=1,j<=Length[rules],j++,
			maxpow=Table[Max[maxpow[[k]],rules[[j,1,k]]],{k,1,Length[vars]}];
		];
		If[Or@@Map[#>0&,maxpow-commalg["baseNum"][deg]],
			If[!silent,Print["No basis elements with appropriate powers of generators"]];
			Return[Indeterminate];
		];
		rules=SparseArray[rules,commalg["baseNum"][deg]];
		diff=ArrayRules[rules-Sum[Subscript[c, i]spanrules[[i]],{i,1,Length[spanrules]}]];
		eqs=DeleteDuplicates[Map[Factor[#[[2]]]==0&,diff]];
		sol=Solve[eqs,Table[Subscript[c, i],{i,1,Length[spanrules]}]];
		If[Length[sol]==0,
			If[!silent,Print["Failed to decompose ",poly]];
			If[debug,
				Print[commalg["gspan"][deg]];
				Print["sol=",sol,", eqs=",eqs];
			];
			Return[Indeterminate];
		];
		If[(Length[sol]>1)&&(!silent),
			Print["Multiple Solutions due to relations in algebra, returning a linear combination"];
		];
		ans=Sum[Subscript[c, i]commalg["gspan"][deg][[i]],{i,1,Length[commalg["gspan"][deg]]}]/.sol[[1]];
		If[debugAll,Print[ans]];
		ans=ans/.Table[Subscript[c, i]->0,{i,1,Length[commalg["gspan"][deg]]}];
		Return[commalg["CanonicalForm"][ans]];
	];
	commalg["DecomposePolynomial"][expr_]:=Module[
		{tab}
	,
		tab=polynomialalg["GetHomogeneous"][expr];
		tab=Map[commalg["DecomposeHomogeneous"],tab];
		Return[Plus@@tab];
	];
	commalg["DecomposeRational"][expr0_]:=Module[
		{num,den,expr}
	,
		expr=Factor[expr0];
		num=Numerator[expr];
		den=Denominator[expr];
		Return[Factor[commalg["DecomposePolynomial"][num]/commalg["DecomposePolynomial"][den]]];
	];
	(*Searching for relations*)
	commalg["GradedRelations"][deg_]:=commalg["GradedRelations"][deg]=Module[
		{span=commalg["gspan"][deg],c,diff,rules,eqs,sol}
	,
		If[Length[span]==0,Return[{}]];
		diff=Sum[Subscript[c, i] span[[i]],{i,1,Length[span]}];
		rules=CoefficientRules[commalg["\[Rho]"][diff],vars];
		eqs=Map[#[[2]]==0&,rules];
		Off[Solve::svars];
		sol=Solve[eqs,Table[Subscript[c, i],{i,1,Length[span]}]];
		On[Solve::svars];
		If[Length[sol]!=1,
			Print["Internal error in GradedRelations, sol=",sol,", span=",span];
			Return[Indeterminate];
		];
		diff=diff/.sol[[1]];
		Return[Map[#[[2]]&,CoefficientRules[diff,Table[Subscript[c, i],{i,1,Length[span]}]]]];
	];
	commalg["gbasis"][deg_]:=commalg["gbasis"][deg]=Module[
		{span=commalg["gspan"][deg],relations=commalg["GradedRelations"][deg],M,M1,ans={},i,j}
	,
		M=Orthogonalize[SparseArray[Table[Coefficient[relations[[i]],span[[j]]],{i,1,Length[relations]},{j,1,Length[span]}],{Length[relations],Length[span]}]];
		For[i=1,i<=Length[span],i++,
			M1=SparseArray[Join[M,{Table[KroneckerDelta[i,j],{j,1,Length[span]}]}]];
			M1=Orthogonalize[M1];
			If[Sum[Abs[M1[[-1,i]]],{i,1,Length[span]}]>0,
				AppendTo[ans,span[[i]]];
				M=M1;
			];
		];
		Return[ans];
	];
	commalg["CanonicalFormSubst"][deg_]:=(commalg["CanonicalFormSubst"][deg]=Module[
		{sol,c,ansatz,rules,eqs,span,basis,resolved,subst={},i,expr}
	,
		span=commalg["gspan"][deg];
		basis=commalg["gbasis"][deg];
		resolved=Complement[span,basis];
		For[i=1,i<=Length[resolved],i++,
			expr=resolved[[i]];
			deg=commalg["Deg"][expr];
			ansatz=Sum[Subscript[c, i]commalg["gbasis"][deg][[i]],{i,1,Length[commalg["gbasis"][deg]]}];
			rules=CoefficientRules[commalg["\[Rho]"][expr-ansatz],vars];
			eqs=Map[#[[2]]==0&,rules];
			sol=Solve[eqs];
			If[Length[sol]!=1,
				Print["Internal error in CanonicalFormSubst, sol=",sol,", expr=",expr,", rules=",rules];
				Return[Indeterminate];
			];
			AppendTo[subst,expr->(ansatz/.sol[[1]])];
		];
		Return[subst];
	];);
	commalg["CanonicalFormAux"][expr_]:=Expand[expr/.commalg["CanonicalFormSubst"][commalg["Deg"][expr]]];
	commalg["CanonicalForm"][expr_]:=Module[
		{tab}
	,
		tab=commalg["GetHomogeneous"][expr];
		tab=Map[commalg["CanonicalFormAux"],tab];
		Return[Plus@@tab];
	];
];

GetDimension[commalg_]:=Module[
	{jac,generators,vars,nsubst}
,
	generators=Map[commalg["\[Rho]"],commalg["generators"]];
	vars=commalg["polynomialalg"]["generators"];
	nsubst=Map[(#->RandomInteger[{100,1000}])&,vars];
	jac=Table[D[generators[[i]],vars[[j]]],{i,1,Length[generators]},{j,1,Length[vars]}];
	Return[MatrixRank[jac/.nsubst]];
];

DefineFilteredBasis[commalg_,generators_,polynomialalg_,\[Rho]_]:=Module[
	{k,vars=polynomialalg["generators"]}
,
	(*Defining coefficient rules for basis elements*)
	commalg["basisrules"][deg_]:=commalg["basisrules"][deg]=Module[
		{rulestab,maxpow=Table[1,Length[vars]],i,base,sparserules,j}
	,
		rulestab=Table[CoefficientRules[(Times@@vars)\[Rho][commalg["fspan"][deg][[i]]],vars],{i,1,Length[commalg["fspan"][deg]]}];
		For[i=1,i<=Length[rulestab],i++,
			For[j=1,j<=Length[rulestab[[i]]],j++,
				maxpow=Table[Max[maxpow[[k]],rulestab[[i,j,1,k]]],{k,1,Length[vars]}];
			];
		];
		commalg["baseNum"][deg]=maxpow;
		sparserules=Table[SparseArray[rulestab[[i]],maxpow],{i,1,Length[rulestab]}];
		Return[sparserules];
	];
	(*Defining decomposition of homogeneous monomials*)
	commalg["DecomposePolynomial"][poly0_]:=Module[
		{deg,basisrules,rules,c,diff,eqs,sol,poly,maxpow=Table[1,Length[vars]],j}
	,
		poly=Factor[poly0];
		If[poly===0,Return[0]];
		deg=polynomialalg["Deg"][poly];
		(*Finding if there are any basis elements in such degree*)
		basisrules=commalg["basisrules"][deg];
		If[Length[basisrules]==0,
			If[!silent,Print["No elements in such degre, ",deg]];
			Return[Indeterminate];
		];
		(*Finding if maximum powers of generators in basis elements are large enough*)
		rules=CoefficientRules[(Times@@vars)poly,vars];
		For[j=1,j<=Length[rules],j++,
			maxpow=Table[Max[maxpow[[k]],rules[[j,1,k]]],{k,1,Length[vars]}];
		];
		If[Or@@Map[#>0&,maxpow-commalg["baseNum"][deg]],
			If[!silent,Print["No basis elements with appropriate powers of generators"]];
			Return[Indeterminate];
		];
		rules=SparseArray[rules,commalg["baseNum"][deg]];
		diff=ArrayRules[rules-Sum[Subscript[c, i]basisrules[[i]],{i,1,Length[basisrules]}]];
		eqs=DeleteDuplicates[Map[Factor[#[[2]]]==0&,diff]];
		sol=Solve[eqs,Table[Subscript[c, i],{i,1,Length[basisrules]}]];
		If[Length[sol]==0,
			If[!silent,Print["Failed to decompose ",poly]];
			If[debug,
				Print[commalg["gspan"][deg]];
				Print["sol=",sol,", eqs=",eqs];
			];
			Return[Indeterminate];
		];
		If[(Length[sol]>1)&&(!silent),
			Print["Multiple Solutions due to relations in algebra, returning a linear combination"];
		];
		Return[(Sum[Subscript[c, i]commalg["gspan"][deg][[i]],{i,1,Length[commalg["gspan"][deg]]}]/.sol[[1]])/.Table[Subscript[c, i]->0,{i,1,Length[basisrules]}]];
	];
];

End[]

Begin["`FinitelyGenerated`"]

silent=False;

ReduceOrder[order_]:=Module[
	{ans={},i}
,
	For[i=1,i<=Length[order],i++,
		If[DeleteCases[RowReduce[Append[ans,order[[i]]]][[-1]],0]!={},
			AppendTo[ans,order[[i]]];
		];
	];
	Return[ans];
];

LexOrder[n_]:=Table[KroneckerDelta[i,j],{i,1,n},{j,1,n}];

DegRevLexOrderAux[n_,degtab_]:=Module[
	{i,j}
,
	Return[ReduceOrder[Join[degtab,Table[If[i<=n-j,1,0],{j,1,n-1},{i,1,n}]]]];
];

DegRevLexOrderAux[n_]:=DegRevLexOrderAux[n,{Table[1,n]}];

DegRevLexOrder[commalg_]:=Module[
	{degtab}
,
	degtab=Map[commalg["Deg"],commalg["generators"]];
	Switch[Depth[degtab],
	2,
		degtab={degtab},
	3,
		degtab=Transpose[degtab],
	_,
		Print["Unexpected depth in degree tab ",degtab];
		Return[Indeterminate];
	];
	Return[DegRevLexOrderAux[Length[commalg["generators"]],degtab]];
];

ProductOrder[orders__]:=Module[
	{ordertab=List[orders]}
,
	ordertab=DeleteCases[ordertab,{}];
	Switch[Length[ordertab],
	0,
		Return[{}],
	1,
		Return[ordertab[[1]]],
	_,
		Return[Fold[ArrayFlatten[{{#,0},{0,#2}}] &, ordertab[[1]], Drop[ordertab,1]]];
	];
];

Define[commalg_]:=Module[
	{i}
,
	If[!ListQ[commalg["generators"]],
		Print["Generators are not defined in ",commalg];
		Return[Indeterminate];
	];
	commalg["GeneratorQ"][expr_]:=(Or@@Map[MatchQ[expr,#]&,commalg["generators"]]);
	If[!ListQ[commalg["relations"]],
		Print["Relations are not defined in ",commalg];
		Return[Indeterminate];
	];
	(*Default coefficient domain is rational functions in parameters*)
	If[$VersionNumber>=12.2,
		If[!ValueQ[commalg["coefficientdomain"],Method->"TrialEvaluation"],commalg["coefficientdomain"]=RationalFunctions]
	,
		If[!ValueQ[commalg["coefficientdomain"]],commalg["coefficientdomain"]=RationalFunctions]
	];
	(*Default weights used for monomial ordering is 1*)
	For[i=1,i<=Length[commalg["generators"]],i++,
		With[
			{x=commalg["generators"][[i]]}
		,
			If[$VersionNumber>=12.2,
				If[!ValueQ[commalg["Deg"][x],Method->"TrialEvaluation"],commalg["Deg"][x]=1]
			,
				If[!ValueQ[commalg["Deg"][x]],commalg["Deg"][x]=1]
			];
		];
	];
	(*Default monomial ordering is weighted degree reverse lexicographic*)
	If[!ListQ[commalg["monomialorder"]],
		commalg["monomialorder"]=DegRevLexOrder[commalg];
	];
	commalg["Weight"][monomial_]:=Module[
		{rules}
	,
		rules=CoefficientRules[monomial,commalg["generators"]];
		If[Length[rules]>1,
			Print["Incorrect input in ",commalg["Weight"],", rules=",rules];
			Return[Indeterminate];
		];
		Return[commalg["monomialorder"] . rules[[1,1]]];
	];
	commalg["WeightLessQ"][monomial1_,monomial2_]:=Module[
		{wt1,wt2,j}
	,
		wt1=commalg["Weight"][monomial1];
		wt2=commalg["Weight"][monomial2];
		For[j=1,j<=Length[wt1],j++,
			If[wt1[[j]]<wt2[[j]],Return[True]];
			If[wt1[[j]]>wt2[[j]],Return[False]];
		];
		Return[False];
	];
	(*Defining Groebner Basis and Canonical Form*)
	If[!ListQ[commalg["gb"]],
		commalg["gb"]:=If[Length[commalg["relations"]]==0,
			{}
		,
			If[!silent,PrintTemporary["Computing Groebner Basis in ",commalg]];
			commalg["gb"]=GroebnerBasis[commalg["relations"],commalg["generators"],MonomialOrder->commalg["monomialorder"],CoefficientDomain->commalg["coefficientdomain"]];
			If[!silent,Print["Length of Groebner Basis in ",commalg," is ",Length[commalg["gb"]]]];
			commalg["gb"]
		];
	];
	commalg["Reduce"][expr_]:=PolynomialReduce[expr,commalg["gb"],commalg["generators"],MonomialOrder->commalg["monomialorder"],CoefficientDomain->commalg["coefficientdomain"]];
	commalg["CanonicalForm"][expr_]:=Collect[commalg["Reduce"][expr][[2]],commalg["generators"],Factor];
	(*Defining Filtration*)
	CommutativeAlgebra`Graded`DefineFiltration[commalg];
	If[!Value[commalg["HomogeneousQ"][]],
		commalg["HomogeneousQ"]=True;
		For[i=1,i<=Length[commalg["relations"]],i++,
			If[Length[DeleteDuplicates[Map[commalg["Deg"],MonomialList[commalg["relations"][[i]],commalg["generators"]]]]]>0,
				commalg["GradedQ"]=False;
				Break[];
			];
		];
	];
	(*Defining basis by degree of the highest term*)
	commalg["gbasis"][deg_?(commalg["InadmissibleGradingQ"])]:={};
	commalg["gbasis"][commalg["ZeroDeg"]]={1};
	commalg["gbasis"][deg_]:=commalg["gbasis"][deg]=Module[
		{ans1,ans2,ans}
	,
		ans1=Select[commalg["generators"],commalg["Deg"][#]==deg&];
		ans2=Table[commalg["generators"][[i]]commalg["gbasis"][deg-commalg["Deg"][commalg["generators"][[i]]]],{i,1,Length[commalg["generators"]]}];
		commalg["gb"];(*Evaluating Groebner basis on a single core before executing Parallel Table*)
		ans=DeleteCases[(*Parallel*)Map[commalg["CanonicalForm"],DeleteDuplicates[Flatten[{ans1,ans2}]]],_Plus];
		ans=DeleteDuplicates[Map[FromCoefficientRules[{CoefficientRules[#,commalg["generators"]][[1,1]]->1},commalg["generators"]]&,ans]];
		Return[Select[ans,commalg["Deg"][#]==deg&]];
	];
	commalg["fbasis"][deg_?(commalg["InadmissibleGradingQ"])]:={};
	commalg["fbasis"][deg_]:=commalg["fbasis"][deg]=If[NumberQ[deg],
		DeleteDuplicates[Join[commalg["fbasis"][deg-1],commalg["gbasis"][deg]]]
	,
		Module[
			{j,deglower,ans={}}
		,
			For[i=1,i<=Length[deg],i++,
				deglower=deg;
				deglower[[i]]-=1;
				ans=DeleteDuplicates[Join[ans,commalg["fbasis"][deglower]]];
			];
			ans=DeleteDuplicates[Join[ans,commalg["gbasis"][deg]]];
			Return[ans]
		]
	];
	(*Define Subleading Monomials*)
	commalg["SortedPowers"][expr_]:=Module[
		{monomials}
	,
		monomials=MonomialList[expr,commalg["generators"],commalg["monomialorder"]];
		Return[Map[FromCoefficientRules[{CoefficientRules[#,commalg["generators"]][[1,1]]->1},commalg["generators"]]&,monomials]];
	];
	commalg["SubleadingMonomials"][monomial_]:=Select[commalg["fbasis"][commalg["Deg"][monomial]],commalg["WeightLessQ"][#,monomial]&];
	(*Conversion to singular*)
	CommutativeAlgebra`ExternalLink`DefineSingularStrings[commalg];
	(*Jacobian Matrix and its minors*)
	commalg["JacobiM"]:=commalg["JacobiM"]=Table[commalg["CanonicalForm"][D[commalg["relations"][[i]],commalg["generators"][[j]]]],{i,1,Length[commalg["relations"]]},{j,1,Length[commalg["generators"]]}];
	commalg["relsubsets"][n_]:=commalg["relsubsets"][n]=Subsets[Table[i,{i,1,Length[commalg["relations"]]}],{n}];
	commalg["varsubsets"][n_]:=commalg["varsubsets"][n]=Subsets[Table[i,{i,1,Length[commalg["generators"]]}],{n}];
	commalg["totalJminors"][n_]:=Length[commalg["varsubsets"][n]]Length[commalg["relsubsets"][n]];
	commalg["minorJ"][n_,num_]:=Module[
		{varsubsetnum,relsubsetnum,num0=num-1}
	,
		varsubsetnum=Mod[num0,Length[commalg["varsubsets"][n]]];
		relsubsetnum=(num0-varsubsetnum)/Length[commalg["varsubsets"][n]];
		Return[commalg["CanonicalForm"][Det[commalg["JacobiM"][[commalg["relsubsets"][n][[relsubsetnum+1]],commalg["varsubsets"][n][[varsubsetnum+1]]]]]]];
	];
	(*Random points*)
	If[!NumberQ[commalg["RandomNumber"][]],
		commalg["RandomNumber"][]:=RandomInteger[{10^2,10^6}];
	];
	commalg["RandomPointCounter"]=0;
	commalg["NewRandomPoint"][]:=(
		If[commalg["realtions"]!={},
			Print["Not yet supported functionality of RandomPoint, relations=",commalg["relations"]];
			Return[Indeterminate];
		];
		commalg["RandomPointHistory"][++commalg["RandomPointCounter"]]=Map[#->commalg["RandomNumber"][]&,commalg["generators"]]
	);
	commalg["RandomPoint"][]:=If[commalg["RandomPointCounter"]==0,
		commalg["NewRandomPoint"][]
	,
		commalg["RandomPointHistory"][commalg["RandomPointCounter"]]
	];
	(*Algebraic rank*)
	commalg["AlgebraicRank"][elements_]:=MatrixRank[Outer[(D[##]/.commalg["RandomPoint"][])&,elements,commalg["generators"]]];
	(*Primitive commutative algebra functionality avoiding Groebner bases*)
	commalg["polynomialalg"]["generators"]=commalg["generators"];
	commalg["polynomialalg"]["Deg"]=commalg["Deg"];
	CommutativeAlgebra`PolynomialAlgebra`Define[commalg["polynomialalg"]];
	commalg["DefiningIdeal"]["commalg"]=commalg["polynomialalg"];
	commalg["DefiningIdeal"]["generators"]=commalg["relations"];
	CommutativeAlgebra`Ideals`Define[commalg["DefiningIdeal"]];
];

TestHomomorphism[algebra1_,algebra2_,subst_]:=Module[
	{i,diff}
,
	For[i=1,i<=Length[algebra1["relations"]],i++,
		diff=algebra2["CanonicalForm"][algebra1["relations"][[i]]/.subst];
		(*Print[{i,diff,algebra1["relations"][[i]]/.subst}];*)
		If[diff=!=0,
			Print["Defining ideal of ",algebra1," is not mapped to defining ideal of ",algebra2,", i=",i];
			Return[False];
		];
	];
	Return[True];
];

DefineHomring[homring_,ring1_,ring2_,\[Phi]subst_]:=(
	homring["generators"]=Join[ring2["generators"],ring1["generators"]];
	homring["monomialorder"]=ProductOrder[ring2["monomialorder"],ring1["monomialorder"]];
	homring["relations"]=Join[Map[#-(#/.\[Phi]subst)&,ring1["generators"]],ring2["relations"]];
	Define[homring];
	homring["kernel"]:=homring["kernel"]=Select[homring["gb"],Intersection[Variables[#],ring2["generators"]]=={}&];
);

End[]

Begin["`Ideals`"]

debug=False;
silent=False;

(*Primitive functionality which avoids computing Groebner basis*)
Define[ideal_]:=(
	(*Stting defaults*)
	If[!NumberQ[ideal["maxdeg"]],
		ideal["maxdeg"]=5;
	];
	If[!BooleanQ[ideal["keepcoeff"]],
		ideal["keepcoeff"]=False
	];
	(*Defining span of the ideal*)
	ideal["fspan"][deg_]:=ideal["fspan"][deg]=Module[
		{coeffdeg,i,ans={}}
	,
		For[i=1,i<=Length[ideal["generators"]],i++,
			coeffdeg=deg-ideal["commalg"]["Deg"][ideal["generators"][[i]],"Top"];
			ans=Join[ans,Map[{#,i}&,ideal["commalg"]["fspan"][coeffdeg]]];
		];
		Return[ans];
	];
	(*Trying to find a combination of generators which represents expr*)
	ideal["GetCoefficientsAux"][expr_,deg_]:=Module[
		{c:=ideal["c"],diff,eqs,sol,ans={},extrasubst,i,coeff,fspan}
	,
		fspan=ideal["fspan"][deg];
		If[debug,Print["fspan=",fspan]];
		diff=expr-Sum[Subscript[c, i] fspan[[i,1]]ideal["generators"][[fspan[[i,2]]]],{i,1,Length[fspan]}];
		If[debug,Print["diff=",diff]];
		eqs=Map[#[[2]]==0&,CoefficientRules[diff,ideal["commalg"]["generators"]],1];
		sol=Solve[eqs,Table[Subscript[c, i],{i,0,Length[fspan]}]];
		If[debug,Print["sol=",sol]];
		If[Length[sol]==0,
			Return[Indeterminate]
		];
		If[Length[sol]>1,
			Print["Unexpected number of solutions of linear equation in ideal[\"GetCoeff\"], sol=",sol];
			Return[Indeterminate]
		];
		sol=sol[[1]];
		If[ideal["keepcoeff"],
			extrasubst={}
		,
			extrasubst=Table[Subscript[c, i]->0,{i,1,Length[fspan]}]
		];
		For[i=1,i<=Length[fspan],i++,
			coeff=Factor[(Subscript[c, i]/.sol)/.extrasubst];
			If[coeff=!=0,
				(*Adding coefficient with generator*)
				AppendTo[ans,{fspan[[i,2]]}->coeff fspan[[i,1]]];
				(*Combining coefficients for the same generator*)
				If[Length[ans]>1,
					If[ans[[-1,1]]==ans[[-2,1]],
						ans[[-2,2]]+=ans[[-1,2]];
						ans=Drop[ans,-1];
					];
				];
			];
		];
		Return[ans];
	];
	ideal["GetCoefficients"][expr_,maxdeg_]:=Module[
		{deg,ans,progresscounter}
	,
		progresscounter=PrintTemporary[Dynamic[deg]];
		For[deg=0,deg<=maxdeg,deg++,
			ans=ideal["GetCoefficientsAux"][expr,deg];
			If[ans=!=Indeterminate,
				NotebookDelete[progresscounter];
				Return[ans]
			];
		];
		NotebookDelete[progresscounter];
		Return[Indeterminate];
	];
	ideal["GetCoefficients"][expr_]:=ideal["GetCoefficients"][expr,ideal["maxdeg"]];
);

End[]

Begin["`ExternalLink`"]

(*Parameters for variable names*)
minlength=1;
alphabet=Join[Alphabet[],Alphabet["English","IndexCharacters"]];
prefixname="ShortVarName";
logdir=Global`directory;

PrefixVar[num_]:=Module[
	{indtab}
,
	indtab=IntegerDigits[num-1,Length[alphabet]];
	If[Length[indtab]<1,
		indtab=PadLeft[indtab,1];
	];
	Return[ToExpression[prefixname<>StringJoin@@Map[alphabet[[#+1]]&,indtab]]];
];

PrefixSubst[vars_]:=Module[
	{indexvariable}
,
	Return[Table[vars[[indexvariable]]->PrefixVar[indexvariable],{indexvariable,1,Length[vars]}]];
];

PrefixSubstInverse[vars_]:=Module[
	{indexvariable}
,
	Return[Table[PrefixVar[indexvariable]->vars[[indexvariable]],{indexvariable,1,Length[vars]}]];
];

ClearAll[RemovePrefixSubst,ResorePrefixSubst]

RemovePrefixSubst[num_]:=RemovePrefixSubst[num]=Table[ToString[PrefixVar[i]]->StringDrop[ToString[PrefixVar[i]],StringLength[prefixname]],{i,1,num}];

RestorePrefixSubst[num_]:=ResotrePrefixSubst[num]=Map[#[[2]]->#[[1]]&,RemovePrefixSubst[num]];

(*Interface with Singular*)

DefineSingularStrings[commalg_]:=(
	(*Conversion of generators*)
	commalg["PrefixSubst"]=PrefixSubst[commalg["generators"]];
	commalg["PrefixSubstInverse"]=PrefixSubstInverse[commalg["generators"]];
	commalg["RemovePrefixSubst"]=RemovePrefixSubst[Length[commalg["generators"]]];
	commalg["RestorePrefixSubst"]=RestorePrefixSubst[Length[commalg["generators"]]];
	(*Conversion of lists of expressions*)
	commalg["SingularString"][elements_List]:=StringReplace[
		ToString[InputForm[Expand[elements/.commalg["PrefixSubst"]]]]
	,
		Join[{"{"->"","}"->"","^"->""},commalg["RemovePrefixSubst"]]
	];
	commalg["FromSingularString"][str_String]:=Module[
		{newstr,expr}
	,
		newstr="{"<>StringReplace[str,commalg["RestorePrefixSubst"]]<>"}";
		expr=ToExpression[newstr];
		(*Returning the output depending on whether we had an array or a single element*)
		If[Length[expr]==1,
			expr[[1]]
		,
			expr
		]
	];
);

End[]

Begin["`Mixed`"]

silent=False;

(*Deg[x]={{graded degrees},{filtered degrees}}*)
DefineMixedFiltration[commalg_]:=(
	(*Defining Mixed Grading/Filtration*)
	commalg["DegM"][x_?(NumberQ)]:=Map[0&,commalg["DegM"][commalg["generators"][[1]]]];
	commalg["DegM"][x_Plus]:=Module[
		{xtab=x,ans,gradinglist,filtrationlist,i}
	,
		xtab[[0]]=List;
		ans=Map[commalg["DegM"],xtab];
		(*Testing that polynomial is homogeneous*)
		{gradinglist,filtrationlist}=Transpose[ans];
		If[Length[DeleteDuplicates[gradinglist]]!=1,
			If[!silent,Print["Element ",x," is not homogeneous"]];
			Return[Indeterminate];
		];
		filtrationlist=Reverse[SortBy[filtrationlist,Total]];
		For[i=2,i<=Length[filtrationlist],i++,
			If[Or@@Map[#<0&,filtrationlist[[i]]-filtrationlist[[1]]],
				If[!silent,Print["Element ",x," has no highest filtration component"]];
				Return[Indeterminate];
			];
		];
		Return[{gradinglist[[1]],filtrationlist[[1]]}];
	];
	commalg["DegM"][x_Times]:=Module[
		{xtab=x}
	,
		xtab[[0]]=List;
		Return[Plus@@Map[commalg["Deg"],xtab]];
	];
	commalg["DegM"][x_Power]:=x[[2]]commalg["Deg"][x[[1]]];
	(*Defining Grading and homogeneous components*)
	commalg["Deg"][expr_]:=commalg["DegM"][expr][[1]];
	commalg["GetHomogeneous"][poly_]:=Module[
		{expr=Expand[poly],tab,ans={},degtab={},pos,HandleTerm}
	,
		HandleTerm[monomial_]:=(
			pos=Position[degtab,commalg["Deg"][monomial]];
			Switch[Length[pos],
			0,
				AppendTo[ans,monomial];
				AppendTo[degtab,commalg["Deg"][monomial]],
			1,
				ans[[pos[[1,1]]]]+=monomial,
			_,
				Print["Unexpected Position List in GetHomogeneous, pos=",pos];
				Return[Indeterminate];
			];
		);
		Switch[expr,
		_Plus,
			expr[[0]]=List;
			Map[HandleTerm,expr];
			Return[ans],
		_, 
			Return[{expr}]
		];
	];
);

(*Defining graded/filtered basis for finitenly generated commutative algebra with generators of strictly positive degree*)
DefineMixedSpan[commalg_,SimplifyF_]:=Module[
	{i,j}
,
	(*Defining basis recursively*)
	PosQ[xtab_]:=And@@Map[#>=0&,Flatten[xtab]];
	commalg["mixedspan"][deg_List]:=commalg["mixedspan"][deg]=Module[
		{ans={},k,lbasis,gdeg,fdeg}
	,
		If[DeleteCases[deg,0,2]=={{},{}},Return[{1}]];
		If[DeleteDuplicates[Map[NumberQ,Flatten[deg]]]=!={True},
			Print["Unexpected input in graded basis ",deg];
			Return[Indeterminate];
		];
		If[!PosQ[deg],Return[{}]];
		{gdeg,fdeg}=deg;
		(*Adding all elements of the same gdeg and lower fdeg*)
		For[k=1,k<=Length[fdeg],k++,
			ans=Join[ans,commalg["mixedspan"][{gdeg,fdeg-Table[KroneckerDelta[j,k],{j,1,Length[fdeg]}]}]];
		];
		(*Adding all elements of lower graded degreees*)
		For[k=1,k<=Length[commalg["generators"]],k++,
			lbasis=commalg["mixedspan"][deg-commalg["Deg"][commalg["generators"][[k]]]];
			ans=Join[ans,Map[# commalg["generators"][[k]]&,lbasis]];
		];
		Return[DeleteDuplicates[SimplifyF[ans]]];
	];
];

End[]

EndPackage[]
