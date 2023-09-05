(* ::Package:: *)

BeginPackage["RepresentationAlgebras`"]

Begin["`RepScheme`"]

DefineCatPseudoRepresentation[Rep_,cat_,DimF_,CompositionF_,\[Delta]F_]:=Module[
	{i,j}
,
	With[{SmallCircle=CompositionF}
	,
		Rep[x_?(cat["IdentityMorphismQ"])]:=SparseArray[Table[{i,i}->1,{i,1,DimF[cat["s"][x]]}]];
		Rep[x_Times]:=Module[
			{comm,ncm}
		,
			{comm,ncm}=AbstractAlgebra`GroundField`FactorFieldOut[x,cat["groundfield"]];
			Return[comm Rep[ncm]];
		];
		Rep[x_Plus]:=Module[
			{xtab=x}
		,
			xtab[[0]]=List;
			Return[Total[Map[Rep,xtab]]];
		];
		Rep[x_SmallCircle]:=Rep[x]=Module[
			{xtab=x}
		,
			xtab[[0]]=List;
			Return[Dot[Rep[SmallCircle@@Drop[xtab,-1]],Rep[xtab[[-1]]]]];
		];
		Rep[Global`Inv[x_]]:=Rep[Global`Inv[x]]=\[Delta]F[x] Factor[Inverse[Rep[x]]Det[Rep[x]]];
		Rep[x_CircleTimes]:=Module[
			{xtab=x}
		,
			xtab[[0]]=List;
			Return[TensorProduct@@Map[Rep,xtab]];
		];
	];
];

DefineGroupoidCatRepScheme[Rep_,cat_,commalg_,DimF_,\[Delta]F_]:=Module[
	{i,M}
,
	(*Defining Pseudo Homomorphism to polynomial algebra*)
	DefineCatPseudoRepresentation[Rep,cat,DimF,cat["Composition"],\[Delta]F];
	Rep[x_?(cat["GroupoidGeneratorQ"])]:=Rep[x]=Table[Subscript[x, i,j],{i,1,DimF[cat["t"][x]]},{j,1,DimF[cat["s"][x]]}];
	(*Defining polynomial algebra*)
	commalg["groundfield"]=cat["groundfield"];
	commalg["generators"]=Join[
		Flatten[Variables[Map[Rep,cat["groupoidgenerators"]]]]
	,
		DeleteCases[Map[\[Delta]F,cat["groupoidgenerators"]],_Integer]
	];
	(*Defining relations induced by relations in groupoid*)
	commalg["relations"]={};
	If[ValueQ[cat["relations"]],
		For[i=1,i<=Length[cat["relations"]],i++,
			M=Rep[cat["relations"][[i]]];
			commalg["relations"]=Join[commalg["relations"],Flatten[M]];
		];
	];
];

DefineGroupoidSLnCatRepScheme[Rep_,cat_,commalg_,DimF_]:=(
	DefineGroupoidCatRepScheme[Rep,cat,commalg,DimF,1&];
	(*Defining Grading on polynomial algebra*)
	commalg["Deg"][Subscript[x_?(cat["GroupoidGeneratorQ"]),i_,j_]]:=commalg["Deg"][Subscript[x, i,j]]=cat["Deg"][x];
	(*Adding Det[X]=1 relations*)
	commalg["relations"]=Join[commalg["relations"],Map[(Det[Rep[#]]-1)&,cat["groupoidgenerators"]]];
	(*Initializing commutative algebra*)
	CommutativeAlgebra`FinitelyGenerated`Define[commalg];
);

End[]

EndPackage[]
