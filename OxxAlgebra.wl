(* ::Package:: *)

BeginPackage["OxxAlgebra`"]

(*The first block conatins definitions of generators, relations, and the Mapping Class Group acton on the extended set of generators*)
Begin["`Presentation`"]

Sgn[j_]:=If[j<0,-1,1];

(*Extended set of generators*)
Generators[O_]:={Subscript[O, 1],Subscript[O, 2],Subscript[O, 3],Subscript[O, 4],Subscript[O, 5],Subscript[O, 6],Subscript[O, 1,2],Subscript[O, 2,3],Subscript[O, 3,4],Subscript[O, 4,5],Subscript[O, 5,6],Subscript[O, 6,1],Subscript[O, 1,2,3],Subscript[O, 2,3,4],Subscript[O, 3,4,5]};
(*Normal ordering relations from Table 1 of the paper*)
QCommRelations[O_,Q_,T_,MultiplyF_]:={{Subscript[O, 2],Subscript[O, 1],-1,Subscript[O, 1,2]},{Subscript[O, 3],Subscript[O, 1],0,0},{Subscript[O, 3],Subscript[O, 2],-1,Subscript[O, 2,3]},{Subscript[O, 4],Subscript[O, 1],0,0},{Subscript[O, 4],Subscript[O, 2],0,0},{Subscript[O, 4],Subscript[O, 3],-1,Subscript[O, 3,4]},{Subscript[O, 5],Subscript[O, 1],0,0},{Subscript[O, 5],Subscript[O, 2],0,0},{Subscript[O, 5],Subscript[O, 3],0,0},{Subscript[O, 5],Subscript[O, 4],-1,Subscript[O, 4,5]},{Subscript[O, 6],Subscript[O, 1],1,Subscript[O, 6,1]},{Subscript[O, 6],Subscript[O, 2],0,0},{Subscript[O, 6],Subscript[O, 3],0,0},{Subscript[O, 6],Subscript[O, 4],0,0},{Subscript[O, 6],Subscript[O, 5],-1,Subscript[O, 5,6]},{Subscript[O, 1,2],Subscript[O, 1],1,Subscript[O, 2]},{Subscript[O, 1,2],Subscript[O, 2],-1,Subscript[O, 1]},{Subscript[O, 1,2],Subscript[O, 3],1,Subscript[O, 1,2,3]},{Subscript[O, 1,2],Subscript[O, 4],0,0},{Subscript[O, 1,2],Subscript[O, 5],0,0},{Subscript[O, 1,2],Subscript[O, 6],-1,Subscript[O, 3,4,5]},{Subscript[O, 2,3],Subscript[O, 1],-1,Subscript[O, 1,2,3]},{Subscript[O, 2,3],Subscript[O, 2],1,Subscript[O, 3]},{Subscript[O, 2,3],Subscript[O, 3],-1,Subscript[O, 2]},{Subscript[O, 2,3],Subscript[O, 4],1,Subscript[O, 2,3,4]},{Subscript[O, 2,3],Subscript[O, 5],0,0},{Subscript[O, 2,3],Subscript[O, 6],0,0},{Subscript[O, 2,3],Subscript[O, 1,2],2,((1+Q^4) MultiplyF[Subscript[O, 1],Subscript[O, 3]])/Q^2-((Q^4+T^4) Subscript[O, 5])/(Q^2 T^2)},{Subscript[O, 3,4],Subscript[O, 1],0,0},{Subscript[O, 3,4],Subscript[O, 2],-1,Subscript[O, 2,3,4]},{Subscript[O, 3,4],Subscript[O, 3],1,Subscript[O, 4]},{Subscript[O, 3,4],Subscript[O, 4],-1,Subscript[O, 3]},{Subscript[O, 3,4],Subscript[O, 5],1,Subscript[O, 3,4,5]},{Subscript[O, 3,4],Subscript[O, 6],0,0},{Subscript[O, 3,4],Subscript[O, 1,2],-1,Subscript[O, 5,6]},{Subscript[O, 3,4],Subscript[O, 2,3],2,((1+Q^4) MultiplyF[Subscript[O, 2],Subscript[O, 4]])/Q^2-((Q^4+T^4) Subscript[O, 6])/(Q^2 T^2)},{Subscript[O, 4,5],Subscript[O, 1],0,0},{Subscript[O, 4,5],Subscript[O, 2],0,0},{Subscript[O, 4,5],Subscript[O, 3],-1,Subscript[O, 3,4,5]},{Subscript[O, 4,5],Subscript[O, 4],1,Subscript[O, 5]},{Subscript[O, 4,5],Subscript[O, 5],-1,Subscript[O, 4]},{Subscript[O, 4,5],Subscript[O, 6],1,Subscript[O, 1,2,3]},{Subscript[O, 4,5],Subscript[O, 1,2],0,0},{Subscript[O, 4,5],Subscript[O, 2,3],-1,Subscript[O, 6,1]},{Subscript[O, 4,5],Subscript[O, 3,4],2,((1+Q^4) MultiplyF[Subscript[O, 3],Subscript[O, 5]])/Q^2-((Q^4+T^4) Subscript[O, 1])/(Q^2 T^2)},{Subscript[O, 5,6],Subscript[O, 1],1,Subscript[O, 2,3,4]},{Subscript[O, 5,6],Subscript[O, 2],0,0},{Subscript[O, 5,6],Subscript[O, 3],0,0},{Subscript[O, 5,6],Subscript[O, 4],-1,Subscript[O, 1,2,3]},{Subscript[O, 5,6],Subscript[O, 5],1,Subscript[O, 6]},{Subscript[O, 5,6],Subscript[O, 6],-1,Subscript[O, 5]},{Subscript[O, 5,6],Subscript[O, 1,2],1,Subscript[O, 3,4]},{Subscript[O, 5,6],Subscript[O, 2,3],0,0},{Subscript[O, 5,6],Subscript[O, 3,4],-1,Subscript[O, 1,2]},{Subscript[O, 5,6],Subscript[O, 4,5],2,((1+Q^4) MultiplyF[Subscript[O, 4],Subscript[O, 6]])/Q^2-((Q^4+T^4) Subscript[O, 2])/(Q^2 T^2)},{Subscript[O, 6,1],Subscript[O, 1],-1,Subscript[O, 6]},{Subscript[O, 6,1],Subscript[O, 2],1,Subscript[O, 3,4,5]},{Subscript[O, 6,1],Subscript[O, 3],0,0},{Subscript[O, 6,1],Subscript[O, 4],0,0},{Subscript[O, 6,1],Subscript[O, 5],-1,Subscript[O, 2,3,4]},{Subscript[O, 6,1],Subscript[O, 6],1,Subscript[O, 1]},{Subscript[O, 6,1],Subscript[O, 1,2],-2,((1+Q^4) MultiplyF[Subscript[O, 2],Subscript[O, 6]])/Q^2-((Q^4+T^4) Subscript[O, 4])/(Q^2 T^2)},{Subscript[O, 6,1],Subscript[O, 2,3],1,Subscript[O, 4,5]},{Subscript[O, 6,1],Subscript[O, 3,4],0,0},{Subscript[O, 6,1],Subscript[O, 4,5],-1,Subscript[O, 2,3]},{Subscript[O, 6,1],Subscript[O, 5,6],2,((1+Q^4) MultiplyF[Subscript[O, 1],Subscript[O, 5]])/Q^2-((Q^4+T^4) Subscript[O, 3])/(Q^2 T^2)},{Subscript[O, 1,2,3],Subscript[O, 1],1,Subscript[O, 2,3]},{Subscript[O, 1,2,3],Subscript[O, 2],0,0},{Subscript[O, 1,2,3],Subscript[O, 3],-1,Subscript[O, 1,2]},{Subscript[O, 1,2,3],Subscript[O, 4],1,Subscript[O, 5,6]},{Subscript[O, 1,2,3],Subscript[O, 5],0,0},{Subscript[O, 1,2,3],Subscript[O, 6],-1,Subscript[O, 4,5]},{Subscript[O, 1,2,3],Subscript[O, 1,2],1,Subscript[O, 3]},{Subscript[O, 1,2,3],Subscript[O, 2,3],-1,Subscript[O, 1]},{Subscript[O, 1,2,3],Subscript[O, 3,4],0,-MultiplyF[Subscript[O, 1,2],Subscript[O, 4]]+MultiplyF[Subscript[O, 5,6],Subscript[O, 3]]},{Subscript[O, 1,2,3],Subscript[O, 4,5],1,Subscript[O, 6]},{Subscript[O, 1,2,3],Subscript[O, 5,6],-1,Subscript[O, 4]},{Subscript[O, 1,2,3],Subscript[O, 6,1],0,MultiplyF[Subscript[O, 2,3],Subscript[O, 6]]-MultiplyF[Subscript[O, 4,5],Subscript[O, 1]]},{Subscript[O, 2,3,4],Subscript[O, 1],-1,Subscript[O, 5,6]},{Subscript[O, 2,3,4],Subscript[O, 2],1,Subscript[O, 3,4]},{Subscript[O, 2,3,4],Subscript[O, 3],0,0},{Subscript[O, 2,3,4],Subscript[O, 4],-1,Subscript[O, 2,3]},{Subscript[O, 2,3,4],Subscript[O, 5],1,Subscript[O, 6,1]},{Subscript[O, 2,3,4],Subscript[O, 6],0,0},{Subscript[O, 2,3,4],Subscript[O, 1,2],0,MultiplyF[Subscript[O, 3,4],Subscript[O, 1]]-MultiplyF[Subscript[O, 5,6],Subscript[O, 2]]},{Subscript[O, 2,3,4],Subscript[O, 2,3],1,Subscript[O, 4]},{Subscript[O, 2,3,4],Subscript[O, 3,4],-1,Subscript[O, 2]},{Subscript[O, 2,3,4],Subscript[O, 4,5],0,-MultiplyF[Subscript[O, 2,3],Subscript[O, 5]]+MultiplyF[Subscript[O, 6,1],Subscript[O, 4]]},{Subscript[O, 2,3,4],Subscript[O, 5,6],1,Subscript[O, 1]},{Subscript[O, 2,3,4],Subscript[O, 6,1],-1,Subscript[O, 5]},{Subscript[O, 2,3,4],Subscript[O, 1,2,3],2,MultiplyF[((Q^4+T^4) Subscript[O, 2])/(Q T^2),Subscript[O, 6,1]]+MultiplyF[((1+Q^4) Subscript[O, 4])/Q^2,Subscript[O, 1]]+MultiplyF[((Q^4+T^4) Subscript[O, 6])/(Q^3 T^2),Subscript[O, 1,2]]+MultiplyF[-(((Q^4+T^4) Subscript[O, 2])/(Q^2 T^2)),Subscript[O, 6],Subscript[O, 1]]-((Q^4+T^4) Subscript[O, 3,4,5])/(Q^2 T^2)},{Subscript[O, 3,4,5],Subscript[O, 1],0,0},{Subscript[O, 3,4,5],Subscript[O, 2],-1,Subscript[O, 6,1]},{Subscript[O, 3,4,5],Subscript[O, 3],1,Subscript[O, 4,5]},{Subscript[O, 3,4,5],Subscript[O, 4],0,0},{Subscript[O, 3,4,5],Subscript[O, 5],-1,Subscript[O, 3,4]},{Subscript[O, 3,4,5],Subscript[O, 6],1,Subscript[O, 1,2]},{Subscript[O, 3,4,5],Subscript[O, 1,2],-1,Subscript[O, 6]},{Subscript[O, 3,4,5],Subscript[O, 2,3],0,MultiplyF[Subscript[O, 4,5],Subscript[O, 2]]-MultiplyF[Subscript[O, 6,1],Subscript[O, 3]]},{Subscript[O, 3,4,5],Subscript[O, 3,4],1,Subscript[O, 5]},{Subscript[O, 3,4,5],Subscript[O, 4,5],-1,Subscript[O, 3]},{Subscript[O, 3,4,5],Subscript[O, 5,6],0,MultiplyF[Subscript[O, 1,2],Subscript[O, 5]]-MultiplyF[Subscript[O, 3,4],Subscript[O, 6]]},{Subscript[O, 3,4,5],Subscript[O, 6,1],1,Subscript[O, 2]},{Subscript[O, 3,4,5],Subscript[O, 1,2,3],-2,MultiplyF[((Q^4+T^4) Subscript[O, 1])/(Q T^2),Subscript[O, 5,6]]+MultiplyF[((1+Q^4) Subscript[O, 3])/Q^2,Subscript[O, 6]]+MultiplyF[((Q^4+T^4) Subscript[O, 5])/(Q^3 T^2),Subscript[O, 6,1]]+MultiplyF[-(((Q^4+T^4) Subscript[O, 1])/(Q^2 T^2)),Subscript[O, 5],Subscript[O, 6]]-((Q^4+T^4) Subscript[O, 2,3,4])/(Q^2 T^2)},{Subscript[O, 3,4,5],Subscript[O, 2,3,4],2,MultiplyF[((Q^4+T^4) Subscript[O, 1])/(Q^3 T^2),Subscript[O, 2,3]]+MultiplyF[((Q^4+T^4) Subscript[O, 3])/(Q T^2),Subscript[O, 1,2]]+MultiplyF[((1+Q^4) Subscript[O, 5])/Q^2,Subscript[O, 2]]+MultiplyF[-(((Q^4+T^4) Subscript[O, 3])/(Q^2 T^2)),Subscript[O, 1],Subscript[O, 2]]-((Q^4+T^4) Subscript[O, 1,2,3])/(Q^2 T^2)}};
(*J-relations, six of each of the three types A,B,C*)
JRelationsA[O_,Q_,T_,MultiplyF_]:=Table[Q^-2 MultiplyF[Subscript[O, Mod[i+1,6]+1],Subscript[O, Mod[i+3,6]+1]]+Q^2 MultiplyF[Subscript[O, Mod[i+2,6]+1],Subscript[O, Mod[i+1,6]+1,Mod[i+2,6]+1,Mod[i+3,6]+1]]-MultiplyF[Subscript[O, Mod[i+1,6]+1,Mod[i+2,6]+1],Subscript[O, Mod[i+2,6]+1,Mod[i+3,6]+1]]-(Q^2 T^-2+Q^-2 T^2)Subscript[O, Mod[i-1,6]+1],{i,1,6}];
JRelationsB[O_,Q_,T_,MultiplyF_]:=Table[-Q^-4MultiplyF[Subscript[O, Mod[i+2,6]+1],Subscript[O, Mod[i+4,6]+1,Mod[i-1,6]+1]]-MultiplyF[Subscript[O, Mod[i+3,6]+1],Subscript[O, Mod[i,6]+1,Mod[i+1,6]+1]]+Q^-2 MultiplyF[Subscript[O, Mod[i+2,6]+1,Mod[i+3,6]+1],Subscript[O, Mod[i,6]+1,Mod[i+1,6]+1,Mod[i+2,6]+1]]-(Q^2 T^-2+Q^-2 T^2)(Subscript[O, Mod[i-1,6]+1,Mod[i,6]+1]-Q^-1 MultiplyF[Subscript[O, Mod[i-1,6]+1],Subscript[O, Mod[i,6]+1]]),{i,1,6}];
JRelationsC[O_,Q_,T_,MultiplyF_]:=Table[-Q^2MultiplyF[Subscript[O, Mod[i,6]+1,Mod[i+1,6]+1],Subscript[O, Mod[i+3,6]+1,Mod[i+4,6]+1]]+MultiplyF[Subscript[O, Mod[i-1,6]+1,Mod[i,6]+1,Mod[i+1,6]+1],Subscript[O, Mod[i,6]+1,Mod[i+1,6]+1,Mod[i+2,6]+1]]-Q^-2 MultiplyF[Subscript[O, Mod[i-1,6]+1],Subscript[O, Mod[i+2,6]+1]]
	-(Q^2 T^-2+Q^-2 T^2)(-(Q^4-1+Q^-4) Subscript[O, Mod[i+1,6]+1,Mod[i+2,6]+1,Mod[i+3,6]+1]+Q^-3 MultiplyF[Subscript[O, Mod[i,6]+1],Subscript[O, Mod[i+4,6]+1,Mod[i-1,6]+1]]+Q^3 MultiplyF[Subscript[O, Mod[i+4,6]+1],Subscript[O, Mod[i-1,6]+1,Mod[i,6]+1]]-MultiplyF[Subscript[O, Mod[i-1,6]+1],Subscript[O, Mod[i,6]+1],Subscript[O, Mod[i+4,6]+1]]),{i,1,6}];
JRelations18[O_,Q_,T_,MultiplyF_]:=Join[JRelationsA[O,Q,T,MultiplyF],JRelationsB[O,Q,T,MultiplyF],JRelationsC[O,Q,T,MultiplyF]];
(*Casimir relation*)
QCasimir[O_,Q_,T_,MultiplyF_,Id_]:=(Id (1+T^4) (Q^4+T^4) (Q^8+T^4))/(Q^6 T^6)+1/(6 Q^6 T^2) (-1+Q) (1+Q) (1+Q^2) (Q^4+T^4) (MultiplyF[Subscript[O, 1],Subscript[O, 1]]+MultiplyF[Subscript[O, 2],Subscript[O, 2]]+MultiplyF[Subscript[O, 3],Subscript[O, 3]]+MultiplyF[Subscript[O, 4],Subscript[O, 4]]+MultiplyF[Subscript[O, 5],Subscript[O, 5]]+MultiplyF[Subscript[O, 6],Subscript[O, 6]])-1/(6 Q^6 T^2) (Q^4+2 Q^8+T^4+2 Q^4 T^4) (MultiplyF[Subscript[O, 1,2],Subscript[O, 1,2]]+MultiplyF[Subscript[O, 2,3],Subscript[O, 2,3]]+MultiplyF[Subscript[O, 3,4],Subscript[O, 3,4]]+MultiplyF[Subscript[O, 4,5],Subscript[O, 4,5]]+MultiplyF[Subscript[O, 5,6],Subscript[O, 5,6]]+MultiplyF[Subscript[O, 6,1],Subscript[O, 6,1]])-1/3 Q^2 (MultiplyF[Subscript[O, 1],Subscript[O, 3],Subscript[O, 5]]+MultiplyF[Subscript[O, 2],Subscript[O, 4],Subscript[O, 6]]+MultiplyF[Subscript[O, 3],Subscript[O, 5],Subscript[O, 1]]+MultiplyF[Subscript[O, 4],Subscript[O, 6],Subscript[O, 2]]+MultiplyF[Subscript[O, 5],Subscript[O, 1],Subscript[O, 3]]+MultiplyF[Subscript[O, 6],Subscript[O, 2],Subscript[O, 4]])-1/(6 Q^2) (2+Q^8) (MultiplyF[Subscript[O, 1],Subscript[O, 4],Subscript[O, 3,4,5]]+MultiplyF[Subscript[O, 2],Subscript[O, 5],Subscript[O, 1,2,3]]+MultiplyF[Subscript[O, 3],Subscript[O, 6],Subscript[O, 2,3,4]]+MultiplyF[Subscript[O, 4],Subscript[O, 1],Subscript[O, 3,4,5]]+MultiplyF[Subscript[O, 5],Subscript[O, 2],Subscript[O, 1,2,3]]+MultiplyF[Subscript[O, 6],Subscript[O, 3],Subscript[O, 2,3,4]])+1/(6 Q^5 T^2) (Q^4+2 Q^8+T^4+2 Q^4 T^4) (MultiplyF[Subscript[O, 1],Subscript[O, 6],Subscript[O, 6,1]]+MultiplyF[Subscript[O, 2],Subscript[O, 1],Subscript[O, 1,2]]+MultiplyF[Subscript[O, 3],Subscript[O, 2],Subscript[O, 2,3]]+MultiplyF[Subscript[O, 4],Subscript[O, 3],Subscript[O, 3,4]]+MultiplyF[Subscript[O, 5],Subscript[O, 4],Subscript[O, 4,5]]+MultiplyF[Subscript[O, 6],Subscript[O, 5],Subscript[O, 5,6]])+1/3 (MultiplyF[Subscript[O, 1,2,3],Subscript[O, 2,3,4],Subscript[O, 3,4,5]]+MultiplyF[Subscript[O, 2,3,4],Subscript[O, 3,4,5],Subscript[O, 1,2,3]]+MultiplyF[Subscript[O, 3,4,5],Subscript[O, 1,2,3],Subscript[O, 2,3,4]]);

(*Action of the automorphism Subscript[a, 1] from the mapping class group*)
MCGAction[a_,O_,Q_,MultiplyF_,Inv_]:={{Subscript[a, 1],Subscript[O, 1],Subscript[O, 1]},{Subscript[a, 1],Subscript[O, 2],Q MultiplyF[Subscript[O, 1],Subscript[O, 2]]-Q^2 Subscript[O, 1,2]},{Subscript[a, 1],Subscript[O, 3],Subscript[O, 3]},{Subscript[a, 1],Subscript[O, 4],Subscript[O, 4]},{Subscript[a, 1],Subscript[O, 5],Subscript[O, 5]},{Subscript[a, 1],Subscript[O, 6],Subscript[O, 6,1]},{Subscript[a, 1],Subscript[O, 1,2],Subscript[O, 2]},{Subscript[a, 1],Subscript[O, 2,3],Q MultiplyF[Subscript[O, 1],Subscript[O, 2,3]]-Q^2 Subscript[O, 1,2,3]},{Subscript[a, 1],Subscript[O, 3,4],Subscript[O, 3,4]},{Subscript[a, 1],Subscript[O, 4,5],Subscript[O, 4,5]},{Subscript[a, 1],Subscript[O, 5,6],Subscript[O, 2,3,4]},{Subscript[a, 1],Subscript[O, 6,1],Q MultiplyF[Subscript[O, 1],Subscript[O, 6,1]]-Q^2 Subscript[O, 6]},{Subscript[a, 1],Subscript[O, 1,2,3],Subscript[O, 2,3]},{Subscript[a, 1],Subscript[O, 2,3,4],Q MultiplyF[Subscript[O, 1],Subscript[O, 2,3,4]]-Q^2 Subscript[O, 5,6]},{Subscript[a, 1],Subscript[O, 3,4,5],Subscript[O, 3,4,5]},{Inv[Subscript[a, 1]],Subscript[O, 1],Subscript[O, 1]},{Inv[Subscript[a, 1]],Subscript[O, 2],Subscript[O, 1,2]},{Inv[Subscript[a, 1]],Subscript[O, 3],Subscript[O, 3]},{Inv[Subscript[a, 1]],Subscript[O, 4],Subscript[O, 4]},{Inv[Subscript[a, 1]],Subscript[O, 5],Subscript[O, 5]},{Inv[Subscript[a, 1]],Subscript[O, 6],MultiplyF[Subscript[O, 1],Subscript[O, 6]]/Q-Subscript[O, 6,1]/Q^2},{Inv[Subscript[a, 1]],Subscript[O, 1,2],MultiplyF[Subscript[O, 1],Subscript[O, 1,2]]/Q-Subscript[O, 2]/Q^2},{Inv[Subscript[a, 1]],Subscript[O, 2,3],Subscript[O, 1,2,3]},{Inv[Subscript[a, 1]],Subscript[O, 3,4],Subscript[O, 3,4]},{Inv[Subscript[a, 1]],Subscript[O, 4,5],Subscript[O, 4,5]},{Inv[Subscript[a, 1]],Subscript[O, 5,6],MultiplyF[Subscript[O, 1],Subscript[O, 5,6]]/Q-Subscript[O, 2,3,4]/Q^2},{Inv[Subscript[a, 1]],Subscript[O, 6,1],Subscript[O, 6]},{Inv[Subscript[a, 1]],Subscript[O, 1,2,3],MultiplyF[Subscript[O, 1],Subscript[O, 1,2,3]]/Q-Subscript[O, 2,3]/Q^2},{Inv[Subscript[a, 1]],Subscript[O, 2,3,4],Subscript[O, 5,6]},{Inv[Subscript[a, 1]],Subscript[O, 3,4,5],Subscript[O, 3,4,5]}};

End[]

Begin["`Commutative`"]

DefineOAlgebra[commalg_]:=Module[
	{T:=commalg["T"],JAux,InvJAux,Jsubst,InvJsubst,a1subst,mcgtab,a1Isubst}
,
	(*Defining Commutative Algebra in terms of generators and relations*)
	commalg["generators"]=OxxAlgebra`Presentation`Generators[commalg["O"]];
	commalg["relations"]=OxxAlgebra`Presentation`JRelations18[commalg["O"],1,commalg["T"],Times];
	AppendTo[commalg["relations"],OxxAlgebra`Presentation`QCasimir[commalg["O"],1,commalg["T"],Times,1]];
	commalg["Deg"][commalg["T"]]:=0;
	commalg["Deg"][Subscript[commalg["O"], i__]]:=commalg["Deg"][Subscript[commalg["O"], i]]=Switch[Length[List[i]],
	1,2,
	2,3,
	3,4
	];
	CommutativeAlgebra`FinitelyGenerated`Define[commalg];
	(*Defining Mapping Class Group Action*)
	With[
		{A=commalg["A"],B=commalg["B"],J=commalg["J"],O=commalg["O"],Inv=Global`Inv}
	,
		(*Defining Operator Algebra*)
		If[!ListQ[commalg["mcg"]["groundfield"]["generators"]],
			commalg["mcg"]["groundfield"]["generators"]={T};
		];
		commalg["mcg"]["groupgenerators"]={Subscript[A, 1],J};
		commalg["mcg"]["generators"]=Join[commalg["mcg"]["groupgenerators"],Map[Inv,commalg["mcg"]["groupgenerators"]]];
		(*Defining action on generators*)
		JAux[Subscript[O, i__]]:=Subscript[O, Sequence@@(Mod[List[i],6]+1)];
		InvJAux[Subscript[O, i__]]:=Subscript[O, Sequence@@(Mod[List[i]-2,6]+1)];
		Jsubst=Map[#->JAux[#]&,commalg["generators"]];
		InvJsubst=Map[#->InvJAux[#]&,commalg["generators"]];
		mcgtab=OxxAlgebra`Presentation`MCGAction[A,O,1,Times,Inv];
		a1subst=Map[#[[2]]->#[[3]]&,Select[mcgtab,MatchQ[#,{Subscript[A, 1],__}]&]];
		a1Isubst=Map[#[[2]]->#[[3]]&,Select[mcgtab,MatchQ[#,{Inv[Subscript[A,1]],__}]&]];
		(*Defining full action*)
		commalg["varfield"]["generators"]=Join[commalg["generators"],commalg["mcg"]["groundfield"]["generators"]];
		Subscript[A, 1][x_?(AbstractAlgebra`GroundField`FieldElementQ[#,commalg["varfield"]]&)]:=x/.a1subst;
		Inv[Subscript[A,1]][x_?(AbstractAlgebra`GroundField`FieldElementQ[#,commalg["varfield"]]&)]:=x/.a1Isubst;
		J[x_?(AbstractAlgebra`GroundField`FieldElementQ[#,commalg["varfield"]]&)]:=x/.Jsubst;
		Inv[J][x_?(AbstractAlgebra`GroundField`FieldElementQ[#,commalg["varfield"]]&)]:=x/.InvJsubst;
		Subscript[B, 1][expr_]:=(J\[SmallCircle]Subscript[A, 1]\[SmallCircle]Inv[J])[expr];
		Subscript[A, 2][expr_]:=(J\[SmallCircle]Subscript[B, 1]\[SmallCircle]Inv[J])[expr];
		Subscript[B, 2][expr_]:=(J\[SmallCircle]Subscript[A, 2]\[SmallCircle]Inv[J])[expr];
		Subscript[A, 3][expr_]:=(J\[SmallCircle]Subscript[B, 2]\[SmallCircle]Inv[J])[expr];
		Inv[Subscript[B, 1]][expr_]:=(J\[SmallCircle]Inv[Subscript[A, 1]]\[SmallCircle]Inv[J])[expr];
		Inv[Subscript[A, 2]][expr_]:=(J\[SmallCircle]Inv[Subscript[B, 1]]\[SmallCircle]Inv[J])[expr];
		Inv[Subscript[B, 2]][expr_]:=(J\[SmallCircle]Inv[Subscript[A, 2]]\[SmallCircle]Inv[J])[expr];
		Inv[Subscript[A, 3]][expr_]:=(J\[SmallCircle]Inv[Subscript[B, 2]]\[SmallCircle]Inv[J])[expr];
	];
	(*Defining Test Functions*)
	commalg["TestMCGAction"][]:=Module[
		{i,j,diff}
	,
		For[i=1,i<=Length[commalg["mcg"]["groupgenerators"]],i++,
			For[j=1,j<=Length[commalg["relations"]],j++,
				diff=commalg["CanonicalForm"][commalg["mcg"]["groupgenerators"][[i]][commalg["relations"][[j]]]];
				If[diff=!=0,
					Print["Defining ideal is not closed under MCG, ",{commalg["mcg"]["groupgenerators"][[i]],commalg["relations"][[j]]}];
					Return[False];
				];
			];
		];
		Return[True];
	];
	(*Defining Poisson Bracket*)
	Module[
		{Sgn,BRHS,brtab,X1,X2,i}
	,
		Sgn:=OxxAlgebra`Presentation`Sgn;
		BRHS[A_,B_,j_,C_]:=(-(j/2)B A+Sgn[j] C);
		brtab=Map[{#[[1]],#[[2]],BRHS@@#}&,OxxAlgebra`Presentation`QCommRelations[commalg["O"],1,T,Times]];
		For[i=1,i<=Length[brtab],i++,
			X1=brtab[[i,1]];
			X2=brtab[[i,2]];
			commalg["PoissonBracket"][X2,X1]=-brtab[[i,3]];
		];
		PoissonGeometry`FinitelyGenerated`DefineBiderivation[commalg,commalg["PoissonBracket"]];
	];
];

End[]

Begin["`Main`"]

debug=False;
debugAll=False;

DefineFiltrationFromCommutative[algebra_,commalgebra_]:=With[
	{NonCommutativeMultiply=algebra["NonCommutativeMultiply"]}
,
	(*Defining weights on monomials*)
	algebra["GradedOperationQ"][expr_]:=Switch[expr,
		_Times, True,
		_NonCommutativeMultiply, True,
		_, False
	];
	algebra["Deg"][Times]=algebra["Deg"][NonCommutativeMultiply]=0;
	algebra["Deg"][x_?(AbstractAlgebra`GroundField`FieldElementQ[#,algebra["groundfield"]]&)]:=0;
	algebra["Deg"][x_?(algebra["GeneratorQ"])]:=algebra["Deg"][x]=commalgebra["Deg"][x];
	AbstractAlgebra`Filtered`DefineFiltration[algebra];
];

ImposeNormalOrderingRelations[algebra_]:=Module[
	{i,rtab,Sgn,RHS}
,
	With[{NonCommutativeMultiply=algebra["NonCommutativeMultiply"],Q=algebra["Q"]},
		(*Imposing normal ordering relations*)
		Sgn:=OxxAlgebra`Presentation`Sgn;
		RHS[A_,B_,j_,C_]:=Q^(-2j) NonCommutativeMultiply[B,A]+Sgn[j]Q^-j (Q^2-Q^-2) C;
		rtab=Map[{#[[1]],#[[2]],#[[3]],RHS@@#}&,OxxAlgebra`Presentation`QCommRelations[algebra["O"],algebra["Q"],algebra["T"],NonCommutativeMultiply]];
		For[i=1,i<=Length[rtab],i++,
			With[
				{o1=rtab[[i,1]],o2=rtab[[i,2]],j=rtab[[i,3]],o3=AbstractAlgebra`General`NCCollect[rtab[[i,4]],algebra["groundfield"]]}
			,
				NonCommutativeMultiply[x___,o1,o2,y___]:=NonCommutativeMultiply[x,o3,y]+If[algebra["KeepRelators"],Q^-j algebra["parentalg"]["NonCommutativeMultiply"][x,algebra["\[Eta]"][o1,o2],y],0];
			];
		];
	];
];

DefineMappingClassGroupAction[algebra_,mcg_,a_,b_,\[CapitalIota]_,O_,Inv_]:=Module[
	{mcgtab,i}
,
	mcg["groundfield"]=algebra["groundfield"];
	mcg["groupgenerators"]={Subscript[a, 1],\[CapitalIota]};
	(*Defining automorphism of order 6*)
	(*Notations for triple O*)
	Subscript[O, 4,5,6]=Subscript[O, 1,2,3];
	Subscript[O, 5,6,1]=Subscript[O, 2,3,4];
	Subscript[O, 6,1,2]=Subscript[O, 3,4,5];
	\[CapitalIota][Subscript[O, i__]]:=Subscript[O, Sequence@@(Mod[List[i],6]+1)];
	Inv[\[CapitalIota]][Subscript[O, i__]]:=Subscript[O, Sequence@@(Mod[List[i]-2,6]+1)];
	(*Defining Dehn twist Subscript[a, 1]*)
	mcgtab=OxxAlgebra`Presentation`MCGAction[a,O,algebra["Q"],algebra["NonCommutativeMultiply"],Inv];
	For[i=1,i<=Length[mcgtab],i++,
		With[
			{o1=mcgtab[[i,1]],o2=mcgtab[[i,2]],o3=mcgtab[[i,3]]}
		,
			o1[o2]=o3;
		];
	];
	AbstractAlgebra`Homomorphisms`DefineAutomorphismGroupAlgebra[algebra,mcg];
	(*Introducing notations for Dehn Twists*)
	Subscript[b, 1][expr_]:=(\[CapitalIota]\[SmallCircle]Subscript[a, 1]\[SmallCircle]Inv[\[CapitalIota]])[expr];
	Subscript[a, 2][expr_]:=(\[CapitalIota]\[SmallCircle]Subscript[b, 1]\[SmallCircle]Inv[\[CapitalIota]])[expr];
	Subscript[b, 2][expr_]:=(\[CapitalIota]\[SmallCircle]Subscript[a, 2]\[SmallCircle]Inv[\[CapitalIota]])[expr];
	Subscript[a, 3][expr_]:=(\[CapitalIota]\[SmallCircle]Subscript[b, 2]\[SmallCircle]Inv[\[CapitalIota]])[expr];
	Inv[Subscript[b, 1]][expr_]:=(\[CapitalIota]\[SmallCircle]Inv[Subscript[a, 1]]\[SmallCircle]Inv[\[CapitalIota]])[expr];
	Inv[Subscript[a, 2]][expr_]:=(\[CapitalIota]\[SmallCircle]Inv[Subscript[b, 1]]\[SmallCircle]Inv[\[CapitalIota]])[expr];
	Inv[Subscript[b, 2]][expr_]:=(\[CapitalIota]\[SmallCircle]Inv[Subscript[a, 2]]\[SmallCircle]Inv[\[CapitalIota]])[expr];
	Inv[Subscript[a, 3]][expr_]:=(\[CapitalIota]\[SmallCircle]Inv[Subscript[b, 2]]\[SmallCircle]Inv[\[CapitalIota]])[expr];
];

DefineOxxAlgebra[oxxalg_]:=Module[
	{mcgtab}
,
	(*Setting default notations*)
	If[!ListQ[oxxalg["groundfield"]["generators"]],
		oxxalg["groundfield"]["generators"]={oxxalg["Q"],oxxalg["T"],Subscript[oxxalg["c"], __]};
	];
	If[!BooleanQ[oxxalg["KeepRelators"]],
		oxxalg["KeepRelators"]=False;(*By default we simplify expressions without keeping track of relators used. Set to "True" if you want to see all relators used.*)
	];
	If[!NumberQ[oxxalg["QN"]],
		oxxalg["QN"]=7;(*Default numeric vaule of Q which can be used for fast experiments.*)
	];
	If[!NumberQ[oxxalg["TN"]],
		oxxalg["TN"]=11;(*Default numeric value of T which can be used for fast experiments.*)
	];
	If[!NumberQ[oxxalg["maxK"]],
		oxxalg["maxK"]=10;(*Default maximum Chern-Simons level of representation used to terminate numeric search for stable formulas.*)
	];
	(*Defining Commutative Counterpart*)
	oxxalg["commalg"]["O"]=oxxalg["O"];
	oxxalg["commalg"]["T"]=oxxalg["T"];
	oxxalg["commalg"]["coefficientdomain"]=RationalFunctions;
	oxxalg["commalg"]["mcg"]["groundfield"]=DeleteCases[oxxalg["groundfield"],oxxalg["Q"]];
	OxxAlgebra`Commutative`DefineOAlgebra[oxxalg["commalg"]];
	(*Defining Free algebra with 15 generators. Our main algebra A_{q,t} is a quotient of "freealg" by two-sided ideal "Ideal106".*)
	oxxalg["freealg"]["O"]=oxxalg["O"];
	oxxalg["freealg"]["Q"]=oxxalg["Q"];
	oxxalg["freealg"]["T"]=oxxalg["T"];
	oxxalg["freealg"]["Id"]=oxxalg["Id"];
	oxxalg["freealg"]["c"]=oxxalg["c"];
	oxxalg["freealg"]["groundfield"]["generators"]=oxxalg["groundfield"]["generators"];
	oxxalg["freealg"]["generators"]=oxxalg["commalg"]["generators"];
	AbstractAlgebra`FinitelyGenerated`DefineAssociativeAlgebra[oxxalg["freealg"]];
	DefineFiltrationFromCommutative[oxxalg["freealg"],oxxalg["commalg"]];
	AbstractAlgebra`Filtered`DefineStrictlyFiltered[oxxalg["freealg"]];
	DefineMappingClassGroupAction[oxxalg["freealg"],oxxalg["freealg"]["mcg"],oxxalg["freealg"]["a"],oxxalg["freealg"]["b"],oxxalg["freealg"]["\[CapitalIota]"],oxxalg["O"],oxxalg["Inv"]];
	(*Introducing big defining ideal*)
	oxxalg["Ideal106"]["type"]="TwoSided";
	oxxalg["Ideal106"]["algebra"]=oxxalg["freealg"];
	oxxalg["QCommRelations"]=OxxAlgebra`Presentation`QCommRelations[oxxalg["O"],oxxalg["Q"],oxxalg["T"],oxxalg["freealg"]["NonCommutativeMultiply"]];
	oxxalg["NormalOrderingRelation"][num_]:=Module[
		{A,B,j,C,op}
	,
		{A,B,j,C}=oxxalg["QCommRelations"][[num]];
		op=(oxxalg["Q"]^j oxxalg["freealg"]["NonCommutativeMultiply"][A,B]-oxxalg["Q"]^-j oxxalg["freealg"]["NonCommutativeMultiply"][B,A])-(oxxalg["Q"]^2-oxxalg["Q"]^-2)OxxAlgebra`Presentation`Sgn[j]C;
		Return[op];
	];
	oxxalg["Ideal106"]["generators"]=Append[Table[oxxalg["NormalOrderingRelation"][num],{num,1,Length[oxxalg["QCommRelations"]]}],OxxAlgebra`Presentation`QCasimir[O,oxxalg["Q"],oxxalg["T"],oxxalg["freealg"]["NonCommutativeMultiply"],oxxalg["freealg"]["Id"]]];
	(*Setting up cache directory for the big ideal*)
	oxxalg["Ideal106"]["cachedir"]=FileNameJoin[{oxxalg["cachedir"],"Ideal106"}];
	If[DirectoryQ[oxxalg["cachedir"]]&&!DirectoryQ[oxxalg["Ideal106"]["cachedir"]],
		CreateDirectory[oxxalg["Ideal106"]["cachedir"]];
	];
	AbstractAlgebra`Ideals`DefineIdealBasis[oxxalg["Ideal106"],oxxalg["c"],{oxxalg["Q"]->oxxalg["QN"],oxxalg["T"]->oxxalg["TN"]}];
	(*Defining intermediate object "normalalg", with multilinear operation that brings everything to normal ordering relations*)
	(*We are NOT solving word problem in "normalalg" it is used only for internal purposes when we are working with J-relations*)
	If[debug,Print["Defining Algebra of normally ordered expressions."]];
	oxxalg["normalalg"]["O"]=oxxalg["O"];
	oxxalg["normalalg"]["Q"]=oxxalg["Q"];
	oxxalg["normalalg"]["T"]=oxxalg["T"];
	oxxalg["normalalg"]["Id"]=oxxalg["Id"];
	oxxalg["normalalg"]["c"]=oxxalg["c"];
	oxxalg["normalalg"]["groundfield"]["generators"]=oxxalg["groundfield"]["generators"];
	oxxalg["normalalg"]["generators"]=oxxalg["commalg"]["generators"];
	AbstractAlgebra`FinitelyGenerated`DefineAssociativeAlgebra[oxxalg["normalalg"]];
	(*Options for relators are inherited from oxxalg*)
	oxxalg["normalalg"]["KeepRelators"]=oxxalg["KeepRelators"];
	If[oxxalg["normalalg"]["KeepRelators"],
		oxxalg["normalalg"]["parentalg"]=oxxalg["freealg"];
		oxxalg["normalalg"]["\[Eta]"]=oxxalg["\[Eta]"];
		oxxalg["relatorpatterns"]={oxxalg["\[Eta]"][__],oxxalg["\[Rho]"][_],oxxalg["g"][_]};
		AbstractAlgebra`Relators`DefineFormalQuotient[oxxalg["normalalg"]];
	];
	DefineFiltrationFromCommutative[oxxalg["normalalg"],oxxalg["commalg"]];
	ImposeNormalOrderingRelations[oxxalg["normalalg"]];
	AbstractAlgebra`Filtered`DefineStrictlyFiltered[oxxalg["normalalg"]];
	DefineMappingClassGroupAction[oxxalg["normalalg"],oxxalg["normalalg"]["mcg"],oxxalg["normalalg"]["a"],oxxalg["normalalg"]["b"],oxxalg["normalalg"]["\[CapitalIota]"],oxxalg["O"],oxxalg["Inv"]];
	oxxalg["normalalg"]["Commutative"][expr_]:=expr/.{oxxalg["Q"]->1,oxxalg["normalalg"]["NonCommutativeMultiply"]->Times,oxxalg["Id"]->1,oxxalg["Inv"]->(1/#&)};
	oxxalg["normalalg"]["SortedRules"][expr_]:=Module[
		{rules}
	,
		rules=AbstractAlgebra`General`Rules[expr,oxxalg["normalalg"]["groundfield"]];
		rules=Map[{#[[1]],#[[2]],oxxalg["normalalg"]["Commutative"][#[[1]]]}&,rules];
		rules=Sort[rules,oxxalg["commalg"]["WeightLessQ"][#2[[3]],#1[[3]]]&];
		Return[Map[#[[1]]->#[[2]]&,rules,1]];
	];
	(*Deine two-sided ideal with 7 generators. Not currently used anywhere.*)
	If[debug,Print["Defining two-sided ideal with 7 generators."]];
	oxxalg["Ideal7"]["type"]="TwoSided";
	oxxalg["Ideal7"]["algebra"]=oxxalg["normalalg"];
	oxxalg["Ideal7"]["generators"]=Map[
		AbstractAlgebra`General`NCCollect[#,oxxalg["normalalg"]["groundfield"],Factor]&
	,
		OxxAlgebra`Presentation`JRelationsA[O,oxxalg["normalalg"]["Q"],oxxalg["normalalg"]["T"],oxxalg["normalalg"]["NonCommutativeMultiply"]]
	];
	AppendTo[oxxalg["Ideal7"]["generators"],AbstractAlgebra`General`NCCollect[
		OxxAlgebra`Presentation`QCasimir[O,oxxalg["normalalg"]["Q"],oxxalg["normalalg"]["T"],oxxalg["normalalg"]["NonCommutativeMultiply"],oxxalg["normalalg"]["Id"]]
	,
		oxxalg["normalalg"]["groundfield"]
	,
		FullSimplify
	]];
	oxxalg["Ideal7"]["cachedir"]=FileNameJoin[{oxxalg["cachedir"],"Ideal7"}];
	If[DirectoryQ[oxxalg["cachedir"]]&&!DirectoryQ[oxxalg["Ideal7"]["cachedir"]],
		CreateDirectory[oxxalg["Ideal7"]["cachedir"]];
	];
	AbstractAlgebra`Ideals`DefineIdealBasis[oxxalg["Ideal7"],oxxalg["c"],{oxxalg["Q"]->oxxalg["QN"],oxxalg["T"]->oxxalg["TN"]}];
	(*Define two-sided ideal with 19 generators corresponding to J-relations in "normalalg"*)
	If[debug,Print["Defining two-sided ideal with 19 generators."]];
	oxxalg["Ideal19"]["type"]="TwoSided";
	oxxalg["Ideal19"]["algebra"]=oxxalg["normalalg"];
	oxxalg["Ideal19"]["generators"]=Map[
		AbstractAlgebra`General`NCCollect[#,oxxalg["normalalg"]["groundfield"],Factor]&
	,
		OxxAlgebra`Presentation`JRelations18[O,oxxalg["normalalg"]["Q"],oxxalg["normalalg"]["T"],oxxalg["normalalg"]["NonCommutativeMultiply"]]
	];
	AppendTo[oxxalg["Ideal19"]["generators"],AbstractAlgebra`General`NCCollect[
		OxxAlgebra`Presentation`QCasimir[O,oxxalg["normalalg"]["Q"],oxxalg["normalalg"]["T"],oxxalg["normalalg"]["NonCommutativeMultiply"],oxxalg["normalalg"]["Id"]]
	,
		oxxalg["normalalg"]["groundfield"]
	,
		FullSimplify
	]];
	oxxalg["Ideal19"]["cachedir"]=FileNameJoin[{oxxalg["cachedir"],"Ideal19"}];
	If[DirectoryQ[oxxalg["cachedir"]]&&!DirectoryQ[oxxalg["Ideal19"]["cachedir"]],
		CreateDirectory[oxxalg["Ideal19"]["cachedir"]];
	];
	AbstractAlgebra`Ideals`DefineIdealBasis[oxxalg["Ideal19"],oxxalg["c"],{oxxalg["Q"]->oxxalg["QN"],oxxalg["T"]->oxxalg["TN"]}];
	OxxAlgebra`IdealCoefficients`DefineRegularBasis[oxxalg["Ideal19"],{oxxalg["Q"]->oxxalg["QN"],oxxalg["T"]->oxxalg["TN"]}];
	(*Defining Main Associative algebra. All monomials here will be automatically reduced to appropriate linear combinations of  monomial basis elements*)
	If[debug,Print["Defining oxxalg."]];
	oxxalg["generators"]=oxxalg["commalg"]["generators"];
	AbstractAlgebra`FinitelyGenerated`DefineAssociativeAlgebra[oxxalg];
	If[oxxalg["KeepRelators"],
		oxxalg["parentalg"]=oxxalg["freealg"];
		oxxalg["relatorpatterns"]={oxxalg["\[Eta]"][__],oxxalg["\[Rho]"][_],oxxalg["g"][_]};
		AbstractAlgebra`Relators`DefineFormalQuotient[oxxalg];
		oxxalg["From normalalg"][oxxalg["freealg"]["NonCommutativeMultiply"][X__]]:=oxxalg["freealg"]["NonCommutativeMultiply"][X];
		oxxalg["From normalalg"][X_?(oxxalg["normalalg"]["RelatorQ"])]:=X;
	];
	DefineFiltrationFromCommutative[oxxalg,oxxalg["commalg"]];
	ImposeNormalOrderingRelations[oxxalg];
	DefineMappingClassGroupAction[oxxalg,oxxalg["mcg"],oxxalg["a"],oxxalg["b"],oxxalg["\[CapitalIota]"],oxxalg["O"],oxxalg["Inv"]];
	(*Defining homomorphisms to freealg and normalalg*)
	AbstractAlgebra`Homomorphisms`DefineHomomorphismI[oxxalg["To freealg"],oxxalg,oxxalg["freealg"]];
	AbstractAlgebra`Homomorphisms`DefineHomomorphismI[oxxalg["To normalalg"],oxxalg,oxxalg["normalalg"]];
	AbstractAlgebra`Homomorphisms`DefineHomomorphismI[oxxalg["From normalalg"],oxxalg["normalalg"],oxxalg];
	AbstractAlgebra`Homomorphisms`DefineHomomorphismI[oxxalg["normalalg"]["To freealg"],oxxalg["normalalg"],oxxalg["freealg"]];
	(*Defining algebra of difference operators and its finite-dimensional representations*)
	If[debug,Print["Defining presentation in difference operators."]];
	With[
		{Oa=oxxalg["Oa"],Ob=oxxalg["Ob"],O=oxxalg["O"]}
	,
		oxxalg["oalgebra"]["groundfield"]=oxxalg["groundfield"];
		oxxalg["oalgebra"]["generators"]={Subscript[Oa, 1],Subscript[Oa, 2],Subscript[Oa, 3],Subscript[Ob, 1,2],Subscript[Ob, 2,3],Subscript[Ob, 1,3]};
		AbstractAlgebra`CompositionAlgebra`DefineCompositionAlgebra[oxxalg["oalgebra"]];
		(*Homomorphism from oxxalg to oalgebra*)
		oxxalg["\[CapitalPsi]"][Q_]:=oxxalg["\[CapitalPsi]"][Q]=Module[
			{QComm,o,subst2,subst3,qComm}
		,
			With[
				{Compose=oxxalg["oalgebra"]["NonCommutativeMultiply"]}
			,
				QComm[F_,G_]:=(Q Compose[F,G]-Q^-1 Compose[G,F])/(Q^2-Q^-2)
			];
			Subscript[o, i_]:=Subscript[O, i];
			Subscript[o, i_,j_]:=QComm[Subscript[O, i],Subscript[O, j]];
			Subscript[o, i_,j_,k_]:=QComm[QComm[Subscript[O, i],Subscript[O, j]],Subscript[O, k]];
			subst2={O->o};
			subst3={
				Subscript[O, 1]->Subscript[Oa, 1],Subscript[O, 2]->Subscript[Ob, 1,2],Subscript[O, 3]->Subscript[Oa, 2],
				Subscript[O, 4]->Subscript[Ob, 2,3],Subscript[O, 5]->Subscript[Oa, 3],Subscript[O, 6]->Subscript[Ob, 1,3],
				oxxalg["Q"]->Q
			};
			oxxalg["\[CapitalPsi]Aux"][Q][Subscript[O, jj__]]:=AbstractAlgebra`General`NCCollect[(Subscript[O, jj]/.subst2)/.subst3,oxxalg["oalgebra"]["groundfield"]];
			AbstractAlgebra`Homomorphisms`DefineHomomorphism[oxxalg["\[CapitalPsi]Aux"][Q],oxxalg,oxxalg["oalgebra"]];
			AbstractAlgebra`Homomorphisms`DefineHomomorphism[oxxalg["\[CapitalPsi]Aux"][Q],oxxalg["normalalg"],oxxalg["oalgebra"]];
			AbstractAlgebra`Homomorphisms`DefineHomomorphism[oxxalg["\[CapitalPsi]Aux"][Q],oxxalg["freealg"],oxxalg["oalgebra"]];
			Return[oxxalg["\[CapitalPsi]Aux"][Q]];
		];
		(*Defining Finite Dimensional Representations*)
		oxxalg["TK"][Q_,K_]:=Sqrt[I] Q^(-K/2);
		oxxalg["RepK"][Q_,K_]:=(
			HigherRuijsenaars`FiniteDimensionalModules`GetMCGRep[oxxalg["a"],oxxalg["b"],oxxalg["Oa"],oxxalg["Ob"],oxxalg["oalgebra"]["RepK"][Q,K],Q,K];
			AbstractAlgebra`MatrixRepresentations`DefineRepresentation[oxxalg["oalgebra"]["RepK"][Q,K],oxxalg["oalgebra"]];
			oxxalg["RepK"][Q,K]=oxxalg["oalgebra"]["RepK"][Q,K][oxxalg["\[CapitalPsi]"][Q][#]/.{oxxalg["T"]->oxxalg["TK"][Q,K]}]&;
			Return[oxxalg["RepK"][Q,K]];
		);
		oxxalg["RepKN"][K_]:=oxxalg["RepK"][oxxalg["QN"],K];
		(*Defining Representations in Q-difference operators*)
		oxxalg["xfield"]["generators"]=Join[oxxalg["groundfield"]["generators"],{Subscript[oxxalg["x"], _,_],oxxalg["f"][__]}];
		oxxalg["xFieldQ"][expr_]:=AbstractAlgebra`GroundField`FieldElementQ[expr,oxxalg["xfield"]];
		Subscript[Oa, i_][poly_?(oxxalg["xFieldQ"])]:=Subscript[HigherRuijsenaars`GenusTwo`OA, i][oxxalg["x"],oxxalg["Q"],oxxalg["T"]][poly];
		Subscript[Ob, i_,j_][poly_?(oxxalg["xFieldQ"])]:=(Subscript[oxxalg["x"], i,j]+ Subscript[oxxalg["x"], i,j]^-1)poly;
	];
	(*Loading/Generating Normal Ordered Relations*)
	If[debug,Print["Defining Q-Groebner basis"]];
	oxxalg["GBrel"][num_]:=oxxalg["GBrel"][num]=OxxAlgebra`NCGroebner`CachedGBRelation[num,oxxalg];
	oxxalg["GBsubst"][num_]:=oxxalg["GBsubst"]=Module[
		{lhs,rhs,commlhs}
	,
		commlhs=oxxalg["commalg"]["SortedPowers"][oxxalg["GBrel"][num]/.{oxxalg["normalalg"]["NonCommutativeMultiply"]->Times,oxxalg["normalalg"]["Id"]->1}][[1]];
		lhs=GetNCMonomial[commlhs,oxxalg];
		rhs=AbstractAlgebra`General`NCCollect[lhs-oxxalg["GBrel"][num]/.{oxxalg["Normalalg"]["NonCommutativeMultiply"]->oxxalg["NonCommutativeMultiply"]},oxxalg["groundfield"]];
		Return[lhs->rhs];
	];
	(*Sorting by highest term*)
	oxxalg["Commutative"][expr_]:=expr/.{oxxalg["NonCommutativeMultiply"]->Times,oxxalg["normalalg"]["NonCommutativeMultiply"]->Times,oxxalg["freealg"]["NonCommutativeMultiply"]->Times,oxxalg["Id"]->1,oxxalg["Inv"]->(1/#&),oxxalg["Q"]->1};
	oxxalg["SortedRules"][expr_]:=Module[
		{rules}
	,
		rules=AbstractAlgebra`General`Rules[expr,oxxalg["groundfield"]];
		rules=Map[{#[[1]],#[[2]],oxxalg["Commutative"][#[[1]]]}&,rules];
		rules=Sort[rules,oxxalg["commalg"]["WeightLessQ"][#2[[3]],#1[[3]]]&];
		Return[Map[#[[1]]->#[[2]]&,rules,1]];
	];
	oxxalg["SortedMonomials"][expr_]:=Module[
		{rules}
	,
		rules=oxxalg["SortedRules"][expr];
		Return[Sum[rules[[i,2]]rules[[i,1]],{i,1,Length[rules]}]];
	];
	(*Reducing Higher Terms*)
	oxxalg["normalalg"]["ReducibleNum"][expr_]:=Module[
		{sortedrules,commlead,i,quot}
	,
		sortedrules=oxxalg["normalalg"]["SortedRules"][expr];
		commlead=oxxalg["normalalg"]["Commutative"][sortedrules[[1,1]]];
		For[i=Length[oxxalg["commalg"]["gb"]],i>0,i--,
			quot=Factor[commlead/oxxalg["commalg"]["SortedPowers"][oxxalg["commalg"]["gb"][[i]]][[1]]];
			If[PolynomialQ[quot,oxxalg["commalg"]["generators"]],Break[]];
		];
		Return[{i,quot}];
	];
	oxxalg["NormalReducibleQ"][args___]:=If[DeleteDuplicates[Map[oxxalg["GeneratorQ"],List[args]]]=={True},
		Module[
			{postab,expr}
		,
			(*Checking that monomial is given in its normal form*)
			postab=Map[Position[oxxalg["generators"],#,1][[1]]&,List[args]];
			If[Sort[postab]!=postab,Return[False]];
			expr=oxxalg["normalalg"]["NonCommutativeMultiply"][args];
			Return[oxxalg["normalalg"]["ReducibleNum"][expr][[1]]!=0]
		]
	,
		False
	];
	With[
		{NonCommutativeMultiply=oxxalg["NonCommutativeMultiply"]}
	,
		NonCommutativeMultiply[args__]:=(NonCommutativeMultiply[args]=Module[
			{rules,num,commcofactor,cofactor,fullrules,ans,fullrel,rn,expr,relname}
		,
			expr=oxxalg["normalalg"]["NonCommutativeMultiply"][args];
			rules=oxxalg["normalalg"]["SortedRules"][expr];
			If[debugAll,Print["rules=",rules]];
			rn=oxxalg["normalalg"]["ReducibleNum"][expr];
			If[!ListQ[rn],
				Print["Unexpected output in ReducibleNum, rn=",rn];
				Return[Indeterminate];
			];
			num=rn[[1]];
			commcofactor=rn[[2]];
			If[debugAll,Print["{num,cofactor}=",{num,commcofactor}]];
			cofactor=OxxAlgebra`NCGroebner`GetNCMonomial[commcofactor,oxxalg["normalalg"],oxxalg["commalg"]];
			If[debugAll,Print["cofactor=",cofactor]];
			fullrel=oxxalg["normalalg"]["NonCommutativeMultiply"][cofactor,oxxalg["GBrel"][num]];
			fullrules=oxxalg["normalalg"]["SortedRules"][fullrel];
			If[rules[[1,1]]=!=fullrules[[1,1]],
				Print["Error in simplification of ",expr];
				Print["Sorted rules=",rules];
				Print["Sorted fullrules=",fullrules];
			];
			relname=If[oxxalg["KeepRelators"],
				oxxalg["freealg"]["NonCommutativeMultiply"][oxxalg["normalalg"]["To freealg"][cofactor],oxxalg["g"][num]]
			,
				0
			];
			If[debugAll,Print["relname=",relname]];
			ans=AbstractAlgebra`General`NCCollect[expr-rules[[1,2]]/fullrules[[1,2]](fullrel-relname),oxxalg["normalalg"]["groundfield"]];
			ans=AbstractAlgebra`General`NCCollect[oxxalg["From normalalg"][ans],oxxalg["groundfield"]];
			If[debug,Print[args,"=",ans]];
			Return[ans];
		])/;oxxalg["NormalReducibleQ"][args];
	];
	(*Explicit expressions for relators*)
	(*oxxalg["\[CapitalEta]"][O1_,O2_]:=oxxalg["\[CapitalEta]"]=Module[
		{entries}
	,
		entries=Select[]
	];*)
	oxxalg["\[CapitalRho]"][i_]:=oxxalg["\[CapitalRho]"][i]=
	(*Functions to test relations in defining ideal*)
	oxxalg["ZeroQ"][op0_]:=Module[
		{diff,op}
	,
		op=AbstractAlgebra`General`NCCollect[op0,oxxalg["freealg"]["groundfield"],Factor];
		If[op===0,
			diff=0
		,
			diff=oxxalg["\[CapitalPsi]"][oxxalg["Q"]][op][oxxalg["f"][Subscript[oxxalg["x"], 1,2],Subscript[oxxalg["x"], 2,3],Subscript[oxxalg["x"], 1,3]]];
			diff=Collect[diff,oxxalg["f"][__],Factor];
		];
		Return[diff===0];
	];
	(*Definig LaTex output*)
	OxxAlgebra`LaTex`DefineLaTexOutput[oxxalg];
];

End[]

Begin["`NCGroebner`"]
(*This section contains functions used to search for relations
In particular, here we reconstruct the q-Groebner basis*)
silent=False;(*Will disable all logs in output*)
debugAll=False;(*Enable to see all debug logs in output*)
parallel=False;(*Enable to proceed in parallel, will require (n+1)X memory. Generally doesn't suit for memory-constrained computations.*)

GetQNRelation[expr_,vars_,oxxalg_]:=Module[
	{K,timestart,eqs,subst,genericexpr=expr,sol}
,
	timestart=TimeUsed[];
	For[K=2,K<=oxxalg["maxK"],K++,
		eqs=Map[#[[2]]==0&,Drop[ArrayRules[oxxalg["RepKN"][K][genericexpr]],-1]];
		sol=Solve[eqs,vars];
		If[Length[sol]!=1,
			If[debugAll,Print["K=",K," No relations of the form ",genericexpr]];
			Return[Indeterminate]
		];
		subst=Select[sol[[1]],MatchQ[#,_->0]&];
		If[debugAll,Print["K=",K,", subst=",subst]];
		genericexpr=genericexpr/.subst;
		If[genericexpr===0,Break[]];
	];
	If[debugAll,
		Print["genericexpr=",genericexpr];
		Print["Time used = ",TimeUsed[]-timestart];
	];
	Return[genericexpr];
];

GetQTRelation[expr_,vars_,oxxalg_]:=Module[
	{rules,difftab,fvars,timestart,frules,i,eqs,sol,rhs,rhs2,x:=oxxalg["x"],f:=oxxalg["f"]}
,
	timestart=TimeUsed[];
	If[debugAll,Print["Step 0"]];
	rules=AbstractAlgebra`General`Rules[oxxalg["\[CapitalPsi]"][oxxalg["Q"]][expr],oxxalg["oalgebra"]["groundfield"]];
	(*Print[Short[rules]];*)
	If[debugAll,Print["Step 1, total time used = ",TimeUsed[]-timestart]];
	difftab=Table[rules[[i,1]][f[Subscript[x, 1,2],Subscript[x, 2,3],Subscript[x, 1,3]]],{i,1,Length[rules]}];
	(*Print[Short[difftab]];*)
	If[debugAll,Print["Step 2, total time used = ",TimeUsed[]-timestart]];
	fvars=Select[Variables[difftab],MatchQ[#,f[__]]&];
	(*Print[fvars];*)
	If[debugAll,Print["Step 3, total time used = ",TimeUsed[]-timestart]];
	frules=Table[fvars[[i]]->Sum[Coefficient[difftab[[j]],fvars[[i]]]rules[[j,2]],{j,1,Length[rules]}],{i,1,Length[fvars]}];
	(*Print[Short[frules]];*)
	If[debugAll,Print["Step 4, total time used = ",TimeUsed[]-timestart]];
	If[parallel,
		rhs=ParallelMap[Numerator[Factor[#[[2]]]]&,frules,1,Method->"FinestGrained"]
	,
		rhs=Map[Numerator[Factor[#[[2]]]]&,frules,1]
	];
	(*Print[Short[rhs]];*)
	If[debugAll,Print["Step 5, total time used = ",TimeUsed[]-timestart]];
	rhs2=Flatten[Map[CoefficientRules[#,{Subscript[x, 1,2],Subscript[x, 2,3],Subscript[x, 1,3]}]&,rhs]];
	eqs=Map[#[[2]]==0&,rhs2,1];
	(*Print[Short[eqs]];*)
	If[debugAll,Print["Step 5.5, total time used = ",TimeUsed[]-timestart]];
	sol=Solve[eqs,vars];
	(*Print[Short[sol]];*)
	If[debugAll,Print["Step 6, total time used = ",TimeUsed[]-timestart]];
	If[parallel,
		sol=ParallelMap[Factor,sol,1]
	,
		sol=Map[Factor,sol,1]
	];
	(*Print[Short[sol]];*)
	If[debugAll,Print["Step 7, total time used = ",TimeUsed[]-timestart]];
	If[Length[sol]!=1,
		Print["Unexpected number of solutions in GetQTRelation, sol=",sol];
		Return[Indeterminate];
	];
	Return[(expr/.sol[[1]])/.Map[#->0&,vars]];
];

GetNCMonomial[monomial_,algebra_,commalg_]:=Module[
	{rules,ans=algebra["Id"],i,j}
,
	rules=CoefficientRules[monomial,commalg["generators"]];
	If[Length[rules]>1,
		Print["Unexpected input in GetNCMonomial, rules=",rules];
		Return[Indeterminate];
	];
	For[i=1,i<=Length[rules[[1,1]]],i++,
		ans=algebra["NonCommutativeMultiply"][ans,algebra["NonCommutativeMultiply"]@@Table[algebra["generators"][[i]],{j,1,rules[[1,1,i]]}]];
	];
	Return[ans];
];

GetNCRelation[rel_,oxxalg_,c_]:=Module[
	{monomials,expr,vars,relKN,subleading,rules,exprnormal}
,
	monomials=oxxalg["commalg"]["SortedPowers"][rel];
	If[debugAll,Print[monomials]];
	(*Attempting to find a direct deformation*)
	expr=GetNCMonomial[monomials[[1]],oxxalg["normalalg"],oxxalg["commalg"]]+Sum[Subscript[c, i]GetNCMonomial[monomials[[i]],oxxalg["normalalg"],oxxalg["commalg"]],{i,2,Length[monomials]}];
	If[debugAll,Print["expr=",expr]];
	vars=Table[Subscript[c, i],{i,2,Length[monomials]}];
	If[debugAll,Print["vars=",vars]];
	relKN=GetQNRelation[expr,vars,oxxalg];
	If[debugAll,Print["relKN=",relKN]];
	(*Searching for ansatz with rhs capped by degree of the second monomial*)
	If[(relKN===Indeterminate)&&(oxxalg["commalg"]["Deg"][monomials[[1]]]>oxxalg["commalg"]["Deg"][monomials[[2]]]),
		subleading=oxxalg["commalg"]["fbasis"][oxxalg["commalg"]["Deg"][monomials[[2]]]];
		If[debugAll,Print["Searching for rhs capped by degree of second monomial, number of basis elements = ",Length[subleading]]];
		expr=GetNCMonomial[monomials[[1]],oxxalg["normalalg"],oxxalg["commalg"]]+Sum[Subscript[c, i]GetNCMonomial[subleading[[i]],oxxalg["normalalg"],oxxalg["commalg"]],{i,1,Length[subleading]}];
		vars=Table[Subscript[c, i],{i,1,Length[subleading]}];
		relKN=GetQNRelation[expr,vars,oxxalg];
	];
	(*If failes, looking for general ansatz with the given highest term*)
	If[relKN===Indeterminate,
		subleading=oxxalg["commalg"]["SubleadingMonomials"][monomials[[1]]];
		If[debugAll,Print["Trying general Ansatz, number of basis elements ",Length[subleading]]];
		expr=GetNCMonomial[monomials[[1]],oxxalg["normalalg"],oxxalg["commalg"]]+Sum[Subscript[c, i]GetNCMonomial[subleading[[i]],oxxalg["normalalg"],oxxalg["commalg"]],{i,1,Length[subleading]}];
		vars=Table[Subscript[c, i],{i,1,Length[subleading]}];
		relKN=GetQNRelation[expr,vars,oxxalg];
		If[relKN===Indeterminate,
			Print["Failed to find an NC analogue of relation ",rel];
			Return[Indeterminate];
		];
	];
	(*Finding full Q,T relation*)
	Return[GetQTRelation[relKN,vars,oxxalg]];
];

NormalizeLeadingTerm[poly_,commalg_]:=Module[
	{coeff,leadingterm}
,
	leadingterm=commalg["SortedPowers"][poly][[1]];
	coeff=Coefficient[poly,leadingterm];
	Return[Factor[poly/coeff]];
];

CachedGBRelation[num_,oxxalg_]:=Module[
	{directory,filename,rel,classicalrel,classicaldiff,lead1,lead2,ptemp}
,
	directory=FileNameJoin[{oxxalg["cachedir"],"NCGroebner"}];
	If[DirectoryQ[oxxalg["cachedir"]]&&!DirectoryQ[directory],
		CreateDirectory[directory];
	];
	filename=FileNameJoin[{directory,ToString[num]<>".m"}];
	If[FileExistsQ[filename],
		rel=Import[filename]
	,
		If[!silent,ptemp=PrintTemporary["Calculating q-Groebner relation #",num]];
		rel=GetNCRelation[oxxalg["commalg"]["gb"][[num]],oxxalg,oxxalg["c"]];
		If[!silent,NotebookDelete[ptemp]];
	];
	(*Testing Classical limit*)
	classicalrel=oxxalg["normalalg"]["Commutative"][rel];
	classicaldiff=Factor[classicalrel-NormalizeLeadingTerm[oxxalg["commalg"]["gb"][[num]],oxxalg["commalg"]]];
	If[classicaldiff=!=0,
		Print["Failure in the limit Q->1"];
		Print["oxxalg[\"commalg\"][\"gb\"][[num]]=",oxxalg["commalg"]["gb"][[num]]];
		Print["rel=",rel];
		Print["classical relation ",classicalrel];
		Print["element of GB ",NormalizeLeadingTerm[oxxalg["commalg"]["gb"][[num]],oxxalg["commalg"]]];
		Print["Difference with Q->1 limit = ",classicaldiff];
		Return[Indeterminate]
	];
	(*Checking Leading Terms*)
	lead1=oxxalg["commalg"]["SortedPowers"][rel/.{oxxalg["normalalg"]["NonCommutativeMultiply"]->Times,oxxalg["normalalg"]["Id"]->1}][[1]];
	lead2=oxxalg["commalg"]["SortedPowers"][oxxalg["commalg"]["gb"][[num]]][[1]];
	If[lead1=!=lead2,
		Print["Failure in leading terms ",{lead1,lead2}];
		Return[Indeterminate]
	];
	(*Saving output and returning value*)
	If[!FileExistsQ[filename],
		Export[filename,rel];
	];
	Return[rel];
];

End[]

Begin["`IdealCoefficients`"]

silent=False;
debug=False;
debugAll=False;
maxdeg=13;

(*Attempting to calculatie coefficients for element in defining ideal by directly deforming the classical formula*)
maxextradeg=5;
DeformClassicalCoefficients[rel_,oxxalg_,parametersflag_]:=Module[
	{commrel,commcoeff,coefficients,i,j,deg,c:=oxxalg["c"],ccounter=0,GenericCommF,
	commdiff,commrules,commlhs,M,subst0,b,commsol,GenNum,BasisF,
	candidates={},newcandidates,generator,
	diff,rules,lhs,sol,coeffans,
	ideal,ctab,generators={}}
,
	commrel=oxxalg["Commutative"][rel];
	If[debugAll,Print["commrel=",commrel]];
	(*Finding decomposition of commutative relation*)
	CommutativeAlgebra`Graded`DefineStrictFilteredSpan[oxxalg["commalg"]];(*Defining basis in underlying polynomial algebra*)
	GenericCommF[deg_,basisnum_]:=Module[
		{basis,k,ans=0}
	,
		basis=oxxalg["commalg"]["fspan"][{deg}];
		If[debugAll,Print["GenericCommF: ",{deg,basisnum,basis}]];
		For[k=1,k<=Length[basis],k++,
			ccounter++;
			GenNum[ccounter]=basisnum;
			BasisF[ccounter]=basis[[k]];
			ans+=Subscript[c, ccounter]basis[[k]];
		];
		Return[ans];
	];
	For[deg=oxxalg["commalg"]["Deg"][commrel,"Top"],deg<=oxxalg["commalg"]["Deg"][commrel,"Top"]+maxextradeg,deg++,
		If[debugAll,Print["deg=",deg]];
		commcoeff=Table[GenericCommF[deg-oxxalg["commalg"]["Deg"][oxxalg["commalg"]["relations"][[i]],"Top"],i],{i,1,Length[oxxalg["commalg"]["relations"]]}];
		commdiff=commrel-Sum[commcoeff[[i]]oxxalg["commalg"]["relations"][[i]],{i,1,Length[oxxalg["commalg"]["relations"]]}];
		commrules=CoefficientRules[commdiff,oxxalg["commalg"]["generators"]];
		commlhs=Map[#[[2]]&,commrules];
		If[debugAll,
			Print["ccounter=",ccounter];
			Print["GetNum values ",Table[GenNum[i],{i,1,ccounter}]];
		];
		If[ccounter!=0,
			M=SparseArray[Table[Factor[Coefficient[commlhs[[i]],Subscript[c, j]]],{i,1,Length[commlhs]},{j,1,ccounter}]];
			subst0=Table[Subscript[c, i]->0,{i,1,ccounter}];
			b=-commlhs/.subst0;
			commsol=LinearSolve[M,b];
			If[ListQ[commsol],Break[]];
		];
	];
	If[!ListQ[commsol],
		Print["Failed to find commutative decomposition in DeformClassicalCoefficients[",rel,",",oxxalg,"]"];
		Return[Indeterminate];
	];
	If[debugAll,Print["commsol=",commsol]];
	(*Solving for noncommutative deformation, determining candidates*)
	For[i=1,i<=Length[commsol],i++,
		If[Factor[commsol[[i]]]=!=0,
			generator=oxxalg["Ideal19"]["generators"][[GenNum[i]]];
			AppendTo[generators,generator];
			If[debugAll,Print["generator ",generator]];
			deg=oxxalg["commalg"]["Deg"][BasisF[i]oxxalg["commalg"]["relations"][[GenNum[i]]],"Top"];
			If[debugAll,
				Print[{i,GenNum[i]}];
				Print["commutative counterpart ",oxxalg["commalg"]["relations"][[GenNum[i]]]];
				Print["deg=",deg];
			];
			newcandidates=AbstractAlgebra`Ideals`PrincipalIdealSpanPairs[generator,deg,oxxalg["normalalg"]];
			If[debugAll,Print[generator,", # of new candidates=",Length[newcandidates],", newcandidates=",newcandidates]];
			newcandidates=Select[newcandidates,Factor[oxxalg["Commutative"][#[[1]]#[[2]]]-BasisF[i]]===0&];
			If[debugAll,
				Print["# of candidates after selection =",Length[newcandidates]];
				Print["BasisF[i]=",BasisF[i]];
			];
			candidates=Join[candidates,Map[{#[[1]],GenNum[i],#[[2]]}&,newcandidates]];
		];
	];
	(*Solving small linear system*)
	diff=rel-Sum[Subscript[c, i]oxxalg["normalalg"]["NonCommutativeMultiply"][candidates[[i,1]],oxxalg["Ideal19"]["generators"][[candidates[[i,2]]]],candidates[[i,3]]],{i,1,Length[candidates]}];
	rules=AbstractAlgebra`General`Rules[diff,oxxalg["normalalg"]["groundfield"]];
	lhs=Map[#[[2]]&,rules];
	If[parametersflag,
		sol=Solve[Map[#==0&,lhs],Table[Subscript[c, i],{i,1,Length[candidates]}]];
		If[Length[sol]==0,
			coeffans=Indeterminate
		,
			coeffans=Select[Table[candidates[[i]]->Factor[Subscript[c, i]/.sol[[1]]],{i,1,Length[candidates]}],(#[[2]]=!=0&)];
		]
	,
		M=SparseArray[Table[Factor[Coefficient[lhs[[i]],Subscript[c, j]]],{i,1,Length[lhs]},{j,1,Length[candidates]}]];
		subst0=Table[Subscript[c, i]->0,{i,1,Length[candidates]}];
		b=-lhs/.subst0;
		sol=LinearSolve[M,b];
		If[!ListQ[sol],
			coeffans=Indeterminate
		,
			coeffans=Select[Table[candidates[[i]]->Factor[sol[[i]]],{i,1,Length[candidates]}],(#[[2]]=!=0&)];
		];
	];
	If[coeffans=!=Indeterminate,
		coeffans=Regularize[coeffans,oxxalg];
		Return[coeffans];
	];
	Return[Indeterminate];
];

(*Solving for remaining constants to remove singular part at Q\[Rule]1*)
Regularize[coeff0_,algebra_]:=Module[
		{AnsatzCoeff,c:=algebra["c"],cvars,pcoeff,eqs,sol,ccvars,PrincipalPart,coeff=coeff0,j}
,
		AnsatzCoeff[Subscript[c, i_]]:=Sum[Subscript[c, i,j] (algebra["Q"]-1)^j,{j,0,0}];
		cvars=Select[DeleteDuplicates[Flatten[Map[Variables[#[[2]]]&,coeff]]],MatchQ[#,Subscript[c, _]]&];
		If[debugAll,Print["cvars=",cvars]];
		ccvars=Flatten[Map[AnsatzCoeff,cvars]];
		If[debugAll,Print["ccvars=",ccvars]];
		coeff=coeff/.Map[#->AnsatzCoeff[#]&,cvars];
		If[debugAll,Print["coeff=",coeff]];
		PrincipalPart[expr_]:=Module[
			{lim}
		,
			lim=Limit[expr,algebra["Q"]->1(*,Direction\[Rule]Complexes*)];
			If[debugAll,Print["expr=",expr,", lim=",lim]];
			(*Ugly, but earlier versions of Mathematica don't support Direction\[Rule]Complexes, uncomment the above for Mathematica 12.0 and newer*)
			If[lim===Indeterminate||lim===Infinity||lim===-Infinity||lim===ComplexInfinity,
				Return[Numerator[Factor[Normal[Series[expr,{algebra["Q"],1,-1}]]]]]
			,
				Return[0];
			];
		];
		pcoeff=Map[PrincipalPart[#[[2]]]&,coeff];
		If[debugAll,Print["pcoeff=",pcoeff]];
		eqs=Map[#[[2]]==0&,Flatten[Map[CoefficientRules[#,algebra["Q"]]&,pcoeff,1]]];
		eqs=DeleteCases[eqs,True];
		If[debugAll,Print["eqs=",eqs]];
		If[Length[ccvars]==0,
			If[eqs!={},sol={},sol={{}}]
		,
			sol=Solve[eqs,ccvars];
		];
		If[debugAll,Print["sol=",sol]];
		If[Length[sol]==0,
			If[debug,Print["Failed to find decomposition which is nonsingular at Q->1"]];
			Return[Indeterminate];
		];
		coeff=coeff/.sol[[1]];
		(*Getting rid of free parameters*)
		coeff=coeff/.Map[#->0&,ccvars];
		coeff=Map[#[[1]]->FullSimplify[Factor[#[[2]]]]&,coeff];
		(*Removing elements of the spanning set with zero coefficients*)
		coeff=Select[coeff,(#[[2]]=!=0&)];
		coeff=Table[Take[coeff[[j,1]],3]->FullSimplify[coeff[[j,2]]],{j,1,Length[coeff]}];
		Return[coeff];
];

DefineRegularBasis[ideal_,substN_]:=(
	ideal["RegularSpannedQ"][span_,expr_]:=Module[
		{coeff,coeffrules,i}
	,
		coeff=AbstractAlgebra`Ideals`GetCoefficientsSolve[span,expr,ideal["algebra"]["groundfield"],ideal["algebra"]["c"]];
		If[coeff=!=Indeterminate,
			coeffrules=Table[span[[i]]->coeff[[i]],{i,1,Length[span]}];
			coeffrules=Select[coeffrules,(#[[2]]=!=0)&];
			coeffrules=Regularize[coeffrules,ideal["algebra"]];
		];
		Return[coeffrules=!=Indeterminate];
	];
	ideal["ReduceSpan"][span0_]:=Module[
		{span=span0,i,spanN}
	,
		spanN=span/.substN;
		If[debug,Print["Reducing Span ",Dynamic[i],"/",Length[span]]];
		For[i=1,i<=Length[span],i++,
			If[AbstractAlgebra`Ideals`SpannedQ[Delete[spanN,i],spanN[[i]],ideal["algebra"]["groundfield"],ideal["algebra"]["c"]],
				If[ideal["RegularSpannedQ"][Delete[span,i],span[[i]]],
					span=Delete[span,i];
					spanN=Delete[spanN,i];
					i--;
				];
			];
		];
		Return[span];
	];
	ideal["SelectRegularCandidates"][basis0_,candidates_]:=Module[
		{basis=basis0,basisN,candidatesN,i,reduceflag=False,
		redundancycounter=0,lineardependencycounter=0,ptemp,originallength=-1}
	,
		basisN=basis/.substN;
		candidatesN=candidates/.substN;
		If[debug,
			ptemp=PrintTemporary[Dynamic[{i,redundancycounter,lineardependencycounter}],"/",Length[candidates]]
		];
		For[i=1,i<=Length[candidates],i++,
			If[debugAll,Print["Candidate ",candidates[[i]]]];
			If[!silent&&Global`interfacemode=="BRC"&&RandomInteger[50]==0,
				Print[{i,redundancycounter,lineardependencycounter},"/",Length[candidates]];
			];
			If[!AbstractAlgebra`Ideals`SpannedQ[basisN,candidatesN[[i,4]],ideal["algebra"]["groundfield"],ideal["algebra"]["c"]],
				If[debugAll,Print["Option 1"]];
				AppendTo[basis,candidates[[i]]];
				AppendTo[basisN,candidatesN[[i]]]
			,
				If[debugAll,Print["Option 2"]];
				(*If belongs to the span, checking that decomposition is regular at q\[Rule]1*)
				lineardependencycounter++;
				If[!ideal["RegularSpannedQ"][basis,candidates[[i,4]]],
					If[debugAll,Print["Option A"]];
					reduceflag=True;
					AppendTo[basis,candidates[[i]]];
					AppendTo[basisN,candidatesN[[i]]]
				,
					If[debugAll,Print["Option B"]];
					redundancycounter++
				];
			];
		];
		If[debug,
			NotebookDelete[ptemp];
			ptemp=PrintTemporary["Length of basis before ReduceSpan=",Length[basis]];
		];
		If[reduceflag,
			originallength=Length[basis];
			basis=ideal["ReduceSpan"][basis]
		];
		If[debug,
			NotebookDelete[ptemp];
		];
		If[debug&&Length[candidates]>0,
			Print["Length of basis after ReduceSpan=",Length[basis],"/",originallength,", counters=",{redundancycounter,lineardependencycounter},"/",Length[candidates]];
		];
		Return[basis];
	];
	ideal["PrincipalRegularBasis"][deg_,num_]:=Module[
		{filename,candidates,basis}
	,
		(*Trying to load cached answer*)
		If[DirectoryQ[ideal["cachedir"]],
			filename=FileNameJoin[{ideal["cachedir"],"regular-principal-basis-"<>ToString[{deg,num}]<>".m"}];
			If[FileExistsQ[filename],Return[Import[filename]]];
		];
		(*computing candidates*)
		Switch[ideal["type"],
		"TwoSided",
			candidates=AbstractAlgebra`Ideals`PrincipalIdealSpanPairs[ideal["generators"][[num]],deg,ideal["algebra"]],
		"Left",
			candidates=AbstractAlgebra`Ideals`LeftPrincipalIdealSpanPairs[ideal["generators"][[num]],deg,ideal["algebra"]],
		"Right",
			candidates=AbstractAlgebra`Ideals`LeftPrincipalIdealSpanPairs[ideal["generators"][[num]],deg,ideal["algebra"]],
		_,
			Print["Unexpected ideal type, ",ideal["type"]];
			Return[Indeterminate];
		];
		candidates=Map[ideal["PrecalculateProduct"][num,#]&,candidates,1];
		basis=ideal["SelectRegularCandidates"][ideal["RegularBasis"][deg-1],candidates];
		(*Saving the answer*)
		If[DirectoryQ[ideal["cachedir"]],
			Export[filename,basis];
		];
		Return[basis];
	];
	ideal["RegularBasis"][deg_]:={}/;(deg<0);
	ideal["RegularBasis"][deg_]:=ideal["RegularBasis"][deg]=Module[
		{filename,candidates,lowerbasis,basis,allcandidates}
	,
		(*Trying to load cached answer*)
		If[DirectoryQ[ideal["cachedir"]],
			filename=FileNameJoin[{ideal["cachedir"],"regular-basis-"<>ToString[deg]<>".m"}];
			If[FileExistsQ[filename],Return[Import[filename]]];
		];
		(*Computing regular basis*)
		candidates=Table[ideal["PrincipalRegularBasis"][deg,num],{num,1,Length[ideal["generators"]]}];
		If[debugAll,Print["candidates=",candidates]];
		lowerbasis=Intersection@@Append[candidates,ideal["RegularBasis"][deg-1]];
		If[debugAll,Print["lowerbasis=",lowerbasis]];
		allcandidates=Union@@Table[Complement[candidates[[i]],ideal["RegularBasis"][deg-1]],{i,1,Length[ideal["generators"]]}];
		If[debugAll,Print["allcandidates=",allcandidates]];
		basis=ideal["SelectRegularCandidates"][lowerbasis,allcandidates];
		If[debugAll,Print["basis=",basis]];
		(*Saving the answer*)
		If[DirectoryQ[ideal["cachedir"]],
			Export[filename,basis];
		];
		Return[basis];
	];
);

GetCoefficients[rel_,oxxalg_]:=Module[
	{coeffrules,coeff,ctab,j,deg,basis,
	substN,coeffN,shortbasis,i}
,
	(*Trying to calculate deformation of commutative formula*)
	coeffrules=DeformClassicalCoefficients[rel,oxxalg,True];
	If[coeffrules=!=Indeterminate,
		If[!silent,Print["Deformation of classical decomposition found, attempting to regularize"]];
		coeffrules=Regularize[coeffrules,oxxalg["normalalg"]];
	];
	If[debugAll,Print["Solution for deformation ",coeffrules]];
	If[coeffrules=!=Indeterminate,Return[coeffrules]];
	(*If fails, trying to compute decomposition as generic expression in two-sided ideal in lowest degree*)
	If[!silent,Print["Failed to deform classical coefficients, continuing with LinearSolve and generic ansatz, deg=",Dynamic[deg]]];
	For[deg=oxxalg["normalalg"]["Deg"][rel],deg<=oxxalg["normalalg"]["Deg"][rel]+maxextradeg,deg++,
		If[debugAll,Print["Starting full solution at deg=",deg]];
		basis=oxxalg["Ideal19"]["RegularBasis"][deg];
		(*First attempting to deform numeric solution*)
		substN={oxxalg["Q"]->oxxalg["QN"],oxxalg["T"]->oxxalg["TN"]};
		coeffN=AbstractAlgebra`Ideals`GetCoefficientsSolve[basis/.substN,rel/.substN,oxxalg["normalalg"]["groundfield"],oxxalg["normalalg"]["c"]];
		If[debugAll,Print["coeffN=",coeffN]];
		If[coeffN=!=Indeterminate,
			shortbasis={};
			For[i=1,i<=Length[coeffN],i++,
				If[coeffN=!=0,
					AppendTo[shortbasis,basis[[i]]];
				];
			];
			(*Getting full coefficients*)
			coeff=AbstractAlgebra`Ideals`GetCoefficientsSolve[shortbasis,rel,oxxalg["normalalg"]["groundfield"],oxxalg["normalalg"]["c"]];
			If[debugAll,Print["coeff=",coeff]];
			coeffrules=Table[shortbasis[[i]]->coeff[[i]],{i,1,Length[oxxalg["Ideal19"]["RegularBasis"][deg]]}];
			coeffrules=Select[coeffrules,(#[[2]]=!=0)&];
			If[!silent,
				Print["Direct solution found, attempting to regularize"];
				Print[Short[coeff]];
				Print[Short[coeffrules]];
			];
			coeffrules=Regularize[coeffrules,oxxalg["normalalg"]];
			If[coeffrules=!=Indeterminate,
				If[debugAll,Print["Solution for generic ansatz ",coeffrules]];
				Return[coeffrules]
			];
		];
	];
	(*If failed also, continuing with Solve*)
	If[!silent,Print["Failed to deform classical coefficients, continuing with Solve and generic ansatz, deg=",Dynamic[deg]]];
	For[deg=oxxalg["normalalg"]["Deg"][rel],deg<=oxxalg["normalalg"]["Deg"][rel]+maxextradeg,deg++,
		basis=oxxalg["Ideal19"]["RegularBasis"][deg];
		coeff=AbstractAlgebra`Ideals`GetCoefficientsSolve[basis,rel,oxxalg["normalalg"]["groundfield"],oxxalg["normalalg"]["c"]];
		If[coeff=!=Indeterminate,
			coeffrules=Table[basis[[i]]->coeff[[i]],{i,1,Length[oxxalg["Ideal19"]["RegularBasis"][deg]]}];
			coeffrules=Select[coeffrules,(#[[2]]=!=0)&];
			If[!silent,
				Print["Direct solution found, attempting to regularize"];
				Print[Short[coeff]];
				Print[Short[coeffrules]];
			];
			coeffrules=Regularize[coeffrules,oxxalg["normalalg"]];
			If[coeffrules=!=Indeterminate,
				If[debugAll,Print["Solution for generic ansatz ",coeffrules]];
				Return[coeffrules]
			];
		];
	];
	Return[Indeterminate];
];

CachedGroebnerCoefficients[num_,oxxalg_]:=Module[
	{directory,filename,coeff,lhs,rhs,diff,scoeff}
,
	(*Defining directory where cached calculations are stored*)
	directory=FileNameJoin[{oxxalg["cachedir"],"NCGroebner"}];
	If[DirectoryQ[oxxalg["cachedir"]]&&!DirectoryQ[directory],
		CreateDirectory[directory];
	];
	(*Trying to load cached decomposition formula*)
	filename=FileNameJoin[{directory,"Coeff-"<>"Ideal19"<>"-"<>ToString[num]<>".m"}];
	If[FileExistsQ[filename],
		coeff=Import[filename]
	,
		coeff=GetCoefficients[oxxalg["GBrel"][num],oxxalg];
	];
	(*Checking the decomposition formula*)
	lhs=oxxalg["GBrel"][num];
	rhs=Sum[coeff[[i,2]]oxxalg["normalalg"]["NonCommutativeMultiply"][coeff[[i,1,1]],oxxalg["Ideal19"]["generators"][[coeff[[i,1,2]]]],coeff[[i,1,3]]],{i,1,Length[coeff]}];
	rhs=rhs/.{oxxalg["\[Eta]"]->(0&)};
	diff=AbstractAlgebra`General`NCCollect[lhs-rhs,oxxalg["normalalg"]["groundfield"],Factor];
	If[diff=!=0,
		Print["Error in comparing cached decomposition of Groebner basis element ",num];
		Print["diff=",diff];
		Print["lhs=",lhs];
		Print["rhs=",rhs];
		Return[Indeterminate];
	];
	(*Saving output if necessary*)
	If[!FileExistsQ[filename],
		Export[filename,coeff];
	];
	Return[coeff];
];

End[]

Begin["`LaTex`"]
(*Here we provide functions for automatic conversion of formulas to LaTex*)

debugAll=False;

QTgroundfield["generators"]={Global`Q,Global`T};
qtgroundfield["generators"]={Global`q,Global`t};
qtsubst:=Table[QTgroundfield["generators"][[i]]->qtgroundfield["generators"][[i]]^(1/4),{i,1,Length[QTgroundfield["generators"]]}];
QTsubst:=Table[qtgroundfield["generators"][[i]]->QTgroundfield["generators"][[i]]^4,{i,1,Length[qtgroundfield["generators"]]}];

SignCoeffPowTab[poly_]:=Module[
	{flist,ptab,pow,numtab,cnum,cpow}
,
	flist=FactorList[poly];
	ptab=DeleteCases[flist,{_Plus,_}];
	If[debugAll,Print["Plus removed ptab=",ptab]];
	numtab=Select[ptab,NumberQ[#[[1]]]&];
	If[debugAll,Print["numtab=",numtab]];
	cnum=Times@@Map[#[[1]]^#[[2]]&,numtab,1];
	ptab=DeleteCases[ptab,_?(NumberQ[#[[1]]]&)];
	cpow=Times@@Map[#[[1]]^#[[2]]&,ptab,1];
	Return[{cnum,cpow,Factor[poly/cnum/cpow]}]
];

GetqtRules[normalizedpoly_]:=Module[
	{rules}
,
	rules=CoefficientRules[normalizedpoly,QTgroundfield["generators"]];
	rules=Map[Factor[(#[[1]]/4)]->#[[2]]&,rules];
	Return[rules];
];

FromCoeffRules[rules_,vars_]:=Plus@@Map[Times@@Prepend[Power[vars,#[[1]]],#[[2]]]&,rules];

qtCoeff[coeffQT0_]:=Module[
	{numerator,denominator,coeffQT,numtab,dentab,numrules,denrules,numpoly,denpoly,ans,
	numcoeff,powrulesnum,powrulesden,powtab,diff,qint,tint}
,
	coeffQT=Factor[coeffQT0];
	(*Extracting all powers and numerators from numerator*)
	numerator=Numerator[coeffQT];
	numtab=SignCoeffPowTab[numerator];
	numrules=GetqtRules[numtab[[3]]];
	numpoly=FromCoeffRules[numrules,qtgroundfield["generators"]];
	(*Extracting all powers and numbers from denominator*)
	denominator=Denominator[coeffQT];
	dentab=SignCoeffPowTab[denominator];
	denrules=GetqtRules[dentab[[3]]];
	denpoly=FromCoeffRules[denrules,qtgroundfield["generators"]];
	(*calculating powers of q and t*)
	numcoeff=numtab[[1]]/dentab[[1]];
	powrulesnum=CoefficientRules[numtab[[2]],QTgroundfield["generators"]];
	powrulesden=CoefficientRules[dentab[[2]],QTgroundfield["generators"]];
	If[Length[powrulesnum]!=1||Length[powrulesden]!=1,
		Print["Unexpected QT powers"];
		Print["powrulesnum=",powrulesnum];
		Print["powrulesden=",powrulesden];
		Return[Indeterminate];
	];
	powtab=(powrulesnum[[1,1]]-powrulesden[[1,1]])/4;
	numcoeff=numcoeff powrulesnum[[1,2]]/powrulesden[[1,2]];
	(*Combining answer*)
	ans={Simplify[numcoeff],powtab,Factor[numpoly],Factor[denpoly]};
	(*Absorbing integer power of q into fraction*)
	qint=IntegerPart[ans[[2,1]]];
	If[qint>0&&ans[[3]]=!=1,
		ans[[3]]=Factor[ans[[3]]*qtgroundfield["generators"][[1]]^qint];
		ans[[2,1]]-=qint;
	];
	If[qint<0&&ans[[4]]=!=1,
		ans[[4]]=Factor[ans[[4]]qtgroundfield["generators"][[1]]^(-qint)];
		ans[[2,1]]-=qint;
	];
	(*Absorbing integer power of t into fraction*)
	tint=IntegerPart[ans[[2,2]]];
	If[tint>0&&ans[[3]]=!=1,
		ans[[3]]=Factor[ans[[3]]*qtgroundfield["generators"][[2]]^tint];
		ans[[2,2]]-=tint;
	];
	If[tint<0&&ans[[4]]=!=1,
		ans[[4]]=Factor[ans[[4]]qtgroundfield["generators"][[2]]^(-tint)];
		ans[[2,2]]-=tint;
	];
	(*Checking and returning the answer*)
	diff=Factor[((ans[[1]]QTgroundfield["generators"][[1]]^(4ans[[2,1]])QTgroundfield["generators"][[2]]^(4ans[[2,2]])ans[[3]]/ans[[4]])/.QTsubst)-coeffQT0]/.{Global`Q->7,Global`T->11};
	If[diff=!=0,
		Print["Failure in decomposition of coefficient ",coeffQT0];
		Print["diff=",diff];
		Print["ans=",ans];
		Return[Indeterminate];
	];
	Return[ans];
];

Star[]:=1;
Star[x_]:=x;
Star[x___,Subscript[O, j__],Subscript[O, j__],y___]:=Star[x,Power[Subscript[O, j],2],y];
Star[x___,Power[Subscript[O, j__],pow_],Subscript[O, j__],y___]:=Star[x,Power[Subscript[O, j],pow+1],y];
Star[x___,Subscript[O, j__],Power[Subscript[O, j__],pow_],y___]:=Star[x,Power[Subscript[O, j],pow+1],y];
CombinePowers[expr_]:=expr/.{NonCommutativeMultiply->Star,Diamond->Star,CircleDot->Star};

OString[expr_]:=StringReplace[ToString[TeXForm[CombinePowers[expr]]],{"*"->""}];

MonomialStringTab[ncm_,comm_]:=Module[
	{tab,sign,ans="",numcoeff,frac,qtpowstring=""}
,
	If[debugAll,Print["{comm,ncm}=",{comm,ncm}]];
	tab=qtCoeff[comm];
	If[debugAll,Print["tab=",tab]];
	(*Separating the sign*)
	If[tab[[1]]<0,
		sign=" -";
		numcoeff=Factor[-tab[[1]]]
	,
		sign=" +";
		numcoeff=Factor[tab[[1]]]
	];
	If[numcoeff=!=1,
		ans=ans<>ToString[TeXForm[numcoeff]];
	];
	(*Printing powers of q and t*)
	If[tab[[2,1]]!=0,
		qtpowstring=qtpowstring<>"q^{"<>ToString[TeXForm[tab[[2,1]]]]<>"}";
	];
	If[tab[[2,2]]!=0,
		qtpowstring=qtpowstring<>"t^{"<>ToString[TeXForm[tab[[2,2]]]]<>"}";
	];
	If[tab[[3]]===1&&tab[[4]]=!=1&&qtpowstring!="",
		ans=ans<>"\\frac{"<>qtpowstring<>"}{"<>ToString[TeXForm[tab[[4]]]]<>"}"
	,
		ans=ans<>qtpowstring;
		frac=Factor[tab[[3]]/tab[[4]]];
		If[frac=!=1,
			Switch[frac,
			_Plus,
				ans=ans<>"("<>ToString[TeXForm[frac]]<>")",
			_,
				ans=ans<>ToString[TeXForm[frac]];
			];
		];
	];
	If[ncm=!=1,
		ans=ans<>OString[ncm];
	];
	If[debugAll,
		Print["sign=",sign];
		Print["ans=",ans];
	];
	Return[{sign,ans}];
];

stringsubst={"q^{1}"->"q","t^{1}"->"t",","->""};

BareDenominator[expr_]:=Module[
	{den,factorlist,ans}
,
	den=Denominator[Factor[expr]];
	factorlist=Select[FactorList[den],MatchQ[#[[1]],_Plus]&];
	ans=Factor[Times@@Map[Power@@#&,factorlist,1]];
	Return[ans]
];

SplitRuleAux[x_->y_]:=Switch[y,
_Plus,
	Module[
		{ylist=y}
	,
		ylist[[0]]=List;
		Map[x->#&,ylist]
	],
_,
	{x->y}
];

SplitRules[rules_,T_]:=Module[
	{newrules}
,
	newrules=Map[SplitRuleAux[#[[1]]->Apart[#[[2]],T]]&,rules];
	Flatten[newrules,1]
];

DefineLaTexOutput[oxxalg_]:=(
	oxxalg["SortedString"][expr_]:=Module[
		{rules,stringpairstab}
	,
		rules=oxxalg["SortedRules"][expr/.{oxxalg["Id"]->1}];
		stringpairstab=Flatten[Map[MonomialStringTab[#[[1]],#[[2]]]&,rules,1],1];
		stringpairstab=StringReplace[stringpairstab,stringsubst];
		If[stringpairstab[[1]]==" +",stringpairstab=Drop[stringpairstab,1]];
		Return[StringJoin@@stringpairstab];
	];
	oxxalg["CommutativeString"][expr_]:=Module[
		{rules,stringpairstab}
	,
		rules=CoefficientRules[expr,oxxalg["commalg"]["generators"]];
		rules=Map[Times@@(oxxalg["commalg"]["generators"]^#[[1]])->#[[2]]&,rules];
		rules=Sort[rules,oxxalg["commalg"]["WeightLessQ"][#2[[1]],#1[[1]]]&];
		stringpairstab=Flatten[Map[MonomialStringTab[#[[1]],#[[2]]]&,rules]];
		If[stringpairstab[[1]]==" +",
			stringpairstab=Drop[stringpairstab,1];
		];
		Return[StringReplace[StringJoin[stringpairstab],stringsubst]];
	];
	(*Defining LaTeX output for Ideal19 decomposition*)
	oxxalg["IdealRulesString19Aux"][rules0_]:=Module[
		{MonomialF,expr,rules,stringpairstab,den,formalexpr,i,c,prestring="",ans,n,m,prefactor}
	,
		rules=SortBy[rules0,Mod[#[[1,2]],19]&];
		(*Separating common denominator*)
		den=Denominator[Factor[Sum[Subscript[c, i]rules[[i,2]],{i,1,Length[rules]}]]];
		If[Position[den,Plus]!={},
			rules=Map[#[[1]]->Factor[den #[[2]]]&,rules];
			(*finding fractional powers*)
			{n,m}=Mod[CoefficientRules[rules[[1,2]],QTgroundfield["generators"]][[1,1]],4];
			prefactor=Times@@(QTgroundfield["generators"]^{n,m})/den;
			rules=Map[#[[1]]->Factor[Times@@(QTgroundfield["generators"]^{-n,-m})#[[2]]]&,rules];
			prestring=MonomialStringTab[1,prefactor];
			If[prestring[[1]]==" +",
				prestring=Drop[prestring,1];
			];
			prestring=StringJoin@@prestring;
		];
		(*Calculating rules string*)
		MonomialF[tab_]:=oxxalg["normalalg"]["NonCommutativeMultiply"][tab[[1]],Subscript[oxxalg["\[Rho]"], Mod[tab[[2]],19]],tab[[3]]]/.{oxxalg["Id"]->1};
		stringpairstab=Flatten[Map[MonomialStringTab[MonomialF[#[[1]]],#[[2]]]&,rules]];
		stringpairstab=StringReplace[stringpairstab,stringsubst];
		If[stringpairstab[[1]]==" +",stringpairstab=Drop[stringpairstab,1]];
		If[prestring=="",
			ans=StringJoin@@stringpairstab
		,
			ans=prestring<>"\\left("<>StringJoin@@stringpairstab<>"\\right)"
		];
		Return[ans];
	];
	oxxalg["IdealRulesString19"][rules_]:=Module[
		{splitrules,ans}
	,
		splitrules=GatherBy[rules,BareDenominator[#[[2]]]&];
		splitrules=SortBy[splitrules,-ByteCount[BareDenominator[#[[1,2]]]]&];
		ans=StringJoin@@Flatten[Map[{"+",oxxalg["IdealRulesString19Aux"][#]}&,splitrules]];
		Return[StringDrop[StringReplace[ans,{
			"+-"->"-",
			"\\rho _"->"\\rho_",
			"\\left("->"\\Big(",
			"\\right)"->"\\Big)",
			"\\sqrt{q}"->"q^{\\frac{1}{2}}",
			"\\sqrt[4]{q}"->"q^{\\frac{1}{4}}",
			"q^{"~~N_~~"/"~~D_~~"}":>"q^{\\frac{"~~N~~"}{"~~D~~"}}",
		    "q^{"~~N1_~~N2_~~"/"~~D_~~"}":>"q^{\\frac{"~~N1~~N2~~"}{"~~D~~"}}"
		}],1]];
	];
	(*Defining LaTeX output for Ideal106 decomposition*)
	oxxalg["IdealRulesString106"][rules0_]:=Module[
		{Monomial\[CapitalEta]String,expr,rules,stringpairstab,i,IndexString}
	,
		rules=SortBy[rules0,Mod[#[[1,2]],106]&];
		IndexString[Subscript[oxxalg["O"], i__]]:=StringReplace[ToString[List[i]],{"{"->"","}"->"",","->""," "->""}];
		Monomial\[CapitalEta]String[tab_]:=Module[
			{ans=""}
		,
			If[tab[[1]]=!=oxxalg["Id"],
				ans=ans<>OString[tab[[1]]];
			];
			If[tab[[2]]!=106,
				ans=ans<>"\\eta_{("<>IndexString[oxxalg["QCommRelations"][[tab[[2]],1]]]<>"),("<>IndexString[oxxalg["QCommRelations"][[tab[[2]],2]]]<>")}";
			,
				ans=ans<>"\\rho_0"
			];
			If[tab[[3]]=!=oxxalg["Id"],
				ans=ans<>OString[tab[[3]]];
			];
			Return[ans];
		];
		stringpairstab=Map[MonomialStringTab[1,#[[2]]]&,rules];
		For[i=1,i<=Length[rules],i++,
			If[stringpairstab[[i,2]]=="1",
				stringpairstab[[i,2]]=Monomial\[CapitalEta]String[rules[[i,1]]]
			,
				stringpairstab[[i,2]]=stringpairstab[[i,2]]<>Monomial\[CapitalEta]String[rules[[i,1]]]
			];
		];
		stringpairstab=Flatten[stringpairstab];
		stringpairstab=StringReplace[stringpairstab,stringsubst];
		If[stringpairstab[[1]]==" +",stringpairstab=Drop[stringpairstab,1]];
		Return[StringJoin@@stringpairstab];
	];
);

\[CapitalTau]String[expr_]:=StringReplace[ToString[TeXForm[expr]],{","->"","\\text{**}"->"","*"->"","\\text{Inv}\\left(X_1\\right)"->"X_1^{-1}","\\text{Inv}\\left(X_2\\right)"->"X_2^{-1}","\\text{Inv}\\left(Y_1\\right)"->"Y_1^{-1}","\\text{Inv}\\left(Y_2\\right)"->"Y_2^{-1}"}];

End[]

EndPackage[]

