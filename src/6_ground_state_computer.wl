(* ::Package:: *)

(* ::Title:: *)
(*Ground State Computer*)


(* ::Text:: *)
(*This file is part of the DDF Mathematica Package.*)


(* ::Text:: *)
(*Copyright \[Copyright] 2025 Hannes Malcha*)


(* ::Text:: *)
(*The DDF Package is free software: you can redistribute it and/or modify it under the terms of the GNU General Public License as published by the Free Software Foundation, either version 3 of the License, or (at your option) any later version.*)
(*The DDF Package is distributed in the hope that it will be useful, but WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the GNU General Public License for more details.*)
(*You should have received a copy of the GNU General Public License along with the DDF Package. If not, see https://www.gnu.org/licenses/.*)


(* ::Text:: *)
(*This module defines a function that automatically computes maximal tensor ground states when provided the dominant root of the ground state multiplet and the coset Virasoro eigenvalues of the ground state. *)


(* ::Section:: *)
(*Public Functions from this Module*)


(* ::Text:: *)
(*findTensorStates*)
(*findTensorGroundState*)


(* ::Section:: *)
(*Ground State Computer*)


(* ::Text:: *)
(*The main function needs several auxiliary functions.*)


(* ::Text:: *)
(*This first auxiliary function returns a list of all level 1 DDF states for a given depth and weight.*)


(* ::Input::Initialization:: *)
L1States[depth_,weight_]:=Block[{ket=exp[a[1,weight]],modeSum=depth-weight^2},
partions=IntegerPartitions[modeSum];
Table[ddfProd[Table[A[1,-n],{n,elem}],ket],{elem,partions}]]


(* ::Text:: *)
(*This function is self-descriptive.*)


(* ::Input::Initialization:: *)
mapFunctionAntiSymmetric[fun_,{a___,b_,c_}]:={a,fun[b,c]-fun[c,b]}


(* ::Text:: *)
(*Take a list of DDF states and return a nested ddfTp expression.*)


(* ::Input::Initialization:: *)
listToTp[ddfList_]:=Block[{res=ddfList},
If[Length[res]==1,Return[res[[1]]]];
res=mapFunctionAntiSymmetric[ddfTp,res];
If[Length[res]==1,res[[1]],Fold[ddfTp[#2,#1]&,Reverse[res]]]]


(* ::Text:: *)
(*Remove those elements from a list whose negatives are also in the list.*)


(* ::Input::Initialization:: *)
removeNegatives[list_]:=Module[{seen=<||>},Select[list,Function[x,With[{key=Sort[{x,-x}][[1]]},If[KeyExistsQ[seen,key],False,(seen[key]=True;True)]]]]]


(* ::Text:: *)
(*Find all tensor DDF states for a given level, total depth and total weight.*)


(* ::Input::Initialization:: *)
findTensorStates[{level_,totalDepth_,totalWeight_}]:=Block[{depthList,weightListRules,weightList,dwList,stateList,func},
If[level<=0||totalDepth<0,Return[{}]];
If[level==1,Return[L1States[totalDepth,totalWeight]]];
depthList=Flatten[Map[Permutations,PadRight[#,level]&/@IntegerPartitions[totalDepth,level],1],1];
weightListRules=Table[Solve[Flatten@{Sum[w[i],{i,level}]==totalWeight,Table[w[i]^2<= depth[[i]],{i,level}]},Table[w[i],{i,level}],Integers],{depth, depthList}];
depthList=Table[If[Length[weightListRules[[i]]]==0,{},depthList[[i]]],{i,Length[depthList]}];
depthList=DeleteCases[depthList,{}];
weightListRules=DeleteCases[weightListRules,{}];
If[Length[Flatten[weightListRules]]==0,Return[{}]];
weightList=Table[w[i],{i,level}]/.weightListRules;
dwList=Flatten[Table[Table[{depthList[[i]],weightList[[i]][[j]]},{j,Length[weightList[[i]]]}],{i,Length[depthList]}],1];
stateList=Table[Thread[func[elem[[1]],elem[[2]]]],{elem,dwList}];
stateList=stateList/.func->L1States;
stateList=Flatten[Table[Tuples[elem],{elem,stateList}],1];
stateList=DeleteCases[Table[listToTp[elem],{elem,stateList}],0];
removeNegatives[stateList]
]


(* ::Text:: *)
(*Find the tensor ground state for a given dominant weight and a list of coset Virasoro eigenvalues.*)
(*This function first computes a list of all tensor DDF states with the correct level, depth and weight.*)
(*Subsequently, the specific linear combination of the list of states is identified that is an affine ground state, a coset Virasoro ground state and has the correct coset Virasoro eigenvalues.*)
(*This function makes use of the fact that the affine generators commute with the coset Virasoro operators and that coset Virasoro operators of different levels commute.*)
(*If more than one possible ground state is found a warning is issued.*)


(* ::Input::Initialization:: *)
findTensorGroundState[eigenvalues_,root_]:=Block[{level=root[[1]],states=findTensorStates[{root[[1]],root[[2]],root[[3]]}],length,vec,eqns,eq1,eq2,coefficientList,sol,X},
length=Length[states];
vec=Table[X[i],{i,length}];
eqns={Expand[affineE[0]/@states]};
AppendTo[eqns,Expand[affineE[1]/@states]];
AppendTo[eqns,Expand[affineF[1]/@states]];
AppendTo[eqns,Expand[affineH[1]/@states]];
For[i=2,i<=level,i++,
eq1=Expand[cosetVirasoroOp[i,1]/@states];
eq2=Expand[(cosetVirasoroOp[i,0]/@states)-eigenvalues[[i-1]]states];
AppendTo[eqns,eq1];
AppendTo[eqns,eq2];
];
coefficientList=Flatten[Expand[eqns]];
coefficientList=DeleteCases[DeleteDuplicates[ReplaceAll[Flatten[Table[If[Head[elem]===Plus,Apply[List,elem],elem],{elem,coefficientList}]],n1_*ddfTp[n2_,n3_]->ddfTp[n2,n3]]],0];
sol=Quiet[Solve[Flatten[Table[Table[Coefficient[elem . vec,cf]==0,{cf,coefficientList}],{elem,eqns}]],vec]];
If[Length[sol]>1,Message[findTensorGroundState::msol]];
Expand[ReplaceAll[Sum[X[i]states[[i]],{i,length}]/.sol[[1]],X[i_]->1]]
]


(* ::Input::Initialization:: *)
findTensorGroundState::msol= "Multiple ground states found.";
