(* ::Package:: *)

(* ::Title:: *)
(*DDF Vertex Operators*)


(* ::Text:: *)
(*This file is part of the DDF Mathematica Package.*)


(* ::Text:: *)
(*Copyright \[Copyright] 2025 Hannes Malcha*)


(* ::Text:: *)
(*The DDF Package is free software: you can redistribute it and/or modify it under the terms of the GNU General Public License as published by the Free Software Foundation, either version 3 of the License, or (at your option) any later version.*)
(*The DDF Package is distributed in the hope that it will be useful, but WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the GNU General Public License for more details.*)
(*You should have received a copy of the GNU General Public License along with the DDF Package. If not, see https://www.gnu.org/licenses/.*)


(* ::Text:: *)
(*In order to compute the commutator of two DDF states we must know their Fock state representation. In this module we define the DDF vertex operators that translate between DDF states and Fock states.*)


(* ::Text:: *)
(*The DDF package comes with a large database for the Fock state representation of commonly used DDF states. The database is used to quickly turn DDF States into Fock states and vice versa. This module also introduces the functions for adding data to the table and accessing it.*)


(* ::Section:: *)
(*Public Functions from this Module*)


(* ::Text:: *)
(*opA*)
(*opB*)
(*toTp*)
(*toDDF*)


(* ::Section:: *)
(*DDF Vertex Operators*)


(* ::Text:: *)
(*There are transversal and longitudinal DDF vertex operators. They are both defined as pure functions that may act on other DDF vertex operators or on tachyonic states. The action is given via the commutator defined in the vertex_algebra.wl module.*)


(* ::Text:: *)
(*Transversal DDF vertex operators of level l and mode m as defined in (3.2) of [1].*)


(* ::Input::Initialization:: *)
opA[l_,m_]:=Function[ddfCom[Sqrt[2]^(-1) tp[prod[{s[-1]}],exp[m/l*d]],#]]


(* ::Text:: *)
(*Longitudinal  DDF vertex operators are defined abstractly. The precise definition according to (3.44) of [1] is given in the vertex_algebra.wl module.*)


(* ::Input::Initialization:: *)
opB[l_,m_]:=Function[ddfCom[longitudinalVirasoroOp[l,m],#]]


(* ::Chapter:: *)
(*The Database*)


(* ::Text:: *)
(*The database is used to quickly turn DDF States into Fock states and vice versa. It consists of thousand of .txt files each containing the Fock state corresponding to a given ddfProd, i.e. a product of DDF states acting on a tachyonic state. The .txt files are organized in subfolders according to the level and mode of the states. The files and folders are named such that they can be accessed automatically by extracting information about the level mode and type DDF operators from a given ddfProd.*)


(* ::Section:: *)
(*DDF State to Fock State*)


(* ::Text:: *)
(*Define a function toTp that turns an arbitrary DDF state into a Fock state. toTp takes a linear combination of ddfProd and returns a linear combination of tp. *)
(*To give results quickly toTp will try to read the result from the database. If the desired DDF state is not available in the database the corresponding Fock state is computed.*)


(* ::Text:: *)
(*Make  toTp  linear.*)


(* ::Input::Initialization:: *)
toTp[Plus[a_,b_]]:=toTp[a]+toTp[b]


(* ::Input::Initialization:: *)
toTp[Times[a_, Plus[b_,c_]]]:=toTp[a*c]+toTp[b*c]


(* ::Input::Initialization:: *)
toTp[n_*ddfProd[a_,b_]]:=n*toTp[ddfProd[a,b]]


(* ::Input::Initialization:: *)
toTp[exp[t_]]:=exp[t]


(* ::Input::Initialization:: *)
toTp[n_*exp[t_]]:=n*exp[t]


(* ::Text:: *)
(*Give the main definition.*)
(*The function modeSum computes the sum of the modes of a ddfProd. It is defined in the operator_actions_wl. module.*)


(* ::Input::Initialization:: *)
toTp[ddfProd[ls_, exp[t_]]] := Block[{level = sp[d, t], mode = modeSum[ddfProd[ls, exp[t]]], weight = (1/2)*sp[s, t]}, 
If[level == 1, manualEval[ddfProd[ls, exp[t]]], 
fileName = FileNameJoin[{PackageBaseDirectory,"src", "ddf_states",StringJoin["level_", ToString[level]], StringJoin[ "mode_", ToString[mode]],StringJoin["l", ToString[level], "m", ToString[mode], "n",If[weight>=0,ToString[weight],StringJoin["m",ToString[-weight]]], "_", ddfToNameJoin[ddfProd[ls, exp[t]]], ".txt"]}]; 
     If[FileExistsQ[fileName], ToExpression[Import[fileName]], If[mode>2,Message[toTp::nnarg, n]]; manualEval[ddfProd[ls, exp[t]]]]]]


(* ::Text:: *)
(*The warning message.*)


(* ::Input::Initialization:: *)
toTp::nnarg= "Warning the DDF state is not available in the database. Computing it now. This might take a while.";


(* ::Text:: *)
(*Define the function ddfToName that turns ddfProd[{A_-m1, A_-m2, ... }, exp[state]] into the string Am1Am2.*)


(* ::Input::Initialization:: *)
ddfToName[A[level_,m_]]:=StringJoin["A",ToString[-m]]


(* ::Input::Initialization:: *)
ddfToName[B[level_,m_]]:=StringJoin["B",ToString[-m]]


(* ::Input::Initialization:: *)
ddfToNameJoin[ddfProd[ls_,a_]]:=StringJoin[Table[ddfToName[elem],{elem,ls}]]


(* ::Text:: *)
(*Define the function manualEval that computes the Fock state corresponding to a given DDF state.*)


(* ::Text:: *)
(*The function is defined iteratively.*)


(* ::Input::Initialization:: *)
manualEval[ddfProd[ls_,exp[t_]]]:=Activate[manualEvalIter[ddfProd[ls,exp[t]]]]


(* ::Text:: *)
(*The iterator iterators through the first argument of ddfProd and replaces A[l,m] and B[l,m] by opA[l,m] and B[l,m].*)


(* ::Input::Initialization:: *)
manualEvalIter[ddfProd[{A[level_,m_],ls___},exp[t_]]]:=Inactive[opA][level,m][manualEvalIter[ddfProd[{ls},exp[t]]]]


(* ::Input::Initialization:: *)
manualEvalIter[ddfProd[{B[level_,m_],ls___},exp[t_]]]:=Inactive[opB][level,m][manualEvalIter[ddfProd[{ls},exp[t]]]]


(* ::Input::Initialization:: *)
manualEvalIter[ddfProd[{},exp[t_]]]:=exp[t]


(* ::Section:: *)
(*Fock State to DDF State*)


(* ::Subsection:: *)
(*Generate List of File Names*)


(* ::Text:: *)
(*We define a function fileNamesList that generates a list of all the file names for the DDF states in the database with a given level, mode and weight.*)
(*This function is used to turn a Fock state into a DDF state.*)


(* ::Input::Initialization:: *)
fileNamesList[level_,mode_,weight_]:=Table[FileNameJoin[{PackageBaseDirectory,"src", "ddf_states",StringJoin["level_",ToString[level]],StringJoin["mode_",ToString[mode]],StringJoin["l",ToString[level],"m",ToString[mode],"n",If[weight>=0,ToString[weight],StringJoin["m",ToString[-weight]]],"_",name,".txt"]}],{name,nameTable[mode]}]


(* ::Text:: *)
(*The nameTable function produces all possible combinations Am_1 ... Am_i Bm_i+1 ... Bm_n such that m_1 + ... + m_n = mode*)


(* ::Input::Initialization:: *)
nameTable[mode_]:=Flatten[Table[APartition[doublePartition[mode][[i]][[1]]][BPartition[doublePartition[mode][[i]][[2]]]],{i,mode+1}]]


(* ::Text:: *)
(*doublePartition computes all partitions of i and j for a given n such that n = i + j. Returns a nested list.*)


(* ::Input::Initialization:: *)
doublePartition[mode_]:=Table[{IntegerPartitions[mode-i],IntegerPartitions[i]},{i,0,mode}]


(* ::Text:: *)
(*APartition and BPartition turn the partition m_1 + ... + m_n into the string Am_1 ... Am_n respectively Bm_1 ... Bm_n*)


(* ::Input::Initialization:: *)
APartition[ls1_][ls2_]:=Table[APartitionRecursive["",i][ls2],{i,ls1}]


(* ::Input::Initialization:: *)
BPartition[ls_]:=Table[BPartitionRecursive["",i],{i,ls}]


(* ::Input::Initialization:: *)
APartitionRecursive[string_,ls1_][ls2_]:=APartitionRecursive[StringJoin[string,"A",ToString[ls1[[1]]]],Delete[ls1,1]][ls2]


(* ::Input::Initialization:: *)
BPartitionRecursive[string_,ls_]:=BPartitionRecursive[StringJoin[string,"B",ToString[ls[[1]]]],Delete[ls,1]]


(* ::Input::Initialization:: *)
APartitionRecursive[string_,{}][ls_]:=Map[Function[StringJoin[string,#]],ls]


(* ::Input::Initialization:: *)
BPartitionRecursive[string_,{}]:=string


(* ::Subsection:: *)
(*Generate DDF States*)


(* ::Text:: *)
(*Define a function ddfStateList that returns a list of all ddfProd for a given level, mode and weight.*)


(* ::Input::Initialization:: *)
ddfStatesList[level_,mode_,weight_]:=Flatten[Table[ddfProdMaker[Flatten[{APartitionDDF1[level,doublePartition[mode][[i]][[1]]],BPartitionDDF1[level,doublePartition[mode][[i]][[2]]]}],exp[a[level,weight]]],{i,mode+1}]]


(* ::Text:: *)
(*ddfStateList needs the recursively defined function ddfProdMaker that takes a nested list of APartitionDDF1 and BPartitionDDF1 as an argument and turns it into an ordered ddfProd.*)


(* ::Input::Initialization:: *)
ddfProdMaker[{APartitionDDF1[a_,ls_],ls1__},exp[t_]]:=Table[ddfProdMaker[{APartitionDDF2[a,i],ls1},exp[t]],{i,ls}]


(* ::Input::Initialization:: *)
ddfProdMaker[{ls1___,BPartitionDDF1[a_,ls_]},exp[t_]]:=Table[ddfProdMaker[{ls1,BPartitionDDF2[a,i]},exp[t]],{i,ls}]


(* ::Input::Initialization:: *)
ddfProdMaker[{APartitionDDF2[a_,{}],ls1__},exp[t_]]:=ddfProdMaker[{ls1},exp[t]]


(* ::Input::Initialization:: *)
ddfProdMaker[{ls1__,BPartitionDDF2[a_,{}]},exp[t_]]:=ddfProdMaker[{ls1},exp[t]]


(* ::Input::Initialization:: *)
ddfProdMaker[{APartitionDDF2[a_,ls_],ls1___},exp[t_]]:=ddfProdMaker[Flatten[{Table[A[a,-i],{i,ls}],ls1}],exp[t]]


(* ::Input::Initialization:: *)
ddfProdMaker[{ls1___,BPartitionDDF2[a_,ls_]},exp[t_]]:=ddfProdMaker[Flatten[{ls1,Table[B[a,-i],{i,ls}]}],exp[t]]


(* ::Input::Initialization:: *)
ddfProdMaker[ls_,exp[t_]]:=ddfProd[ls,exp[t]]/;FreeQ[ls,APartitionDDF2]&&FreeQ[ls,BPartitionDDF2]


(* ::Subsection:: *)
(*Fock State to DDF State*)


(* ::Text:: *)
(*Define a function toDDF that turns a Fock state, i.e. a linear combination of tp, into a DDF state, i.e. a linear combination of ddfProd. *)
(*The function only works if the Fock state is an element of the DDF algebra and if the basis of DDF states into which the Fock states transform exist in the database.*)
(*If the transformation is not possible an error message is given and the expression is returned unevaluated.*)


(* ::Input::Initialization:: *)
toDDF[expr_]:=Block[{level=tpInvestigator[expr][[1]],mode=tpInvestigator[expr][[2]],weight=tpInvestigator[expr][[3]]},
If[expr==0,Return[0,Block]];
If[level==1,Message[toDDF::lvl];
expr,
fileNames=fileNamesList[level,mode,weight];
If[Apply[And,Table[FileExistsQ[file],{file,fileNames}]],
states=Table[ToExpression[Import[file]],{file,fileNames}];
len=Length[states];
coefficientList=DeleteCases[DeleteDuplicates[Flatten[Table[ReplaceAll[If[Head[elem]===Plus,Apply[List,elem],elem],n_*tp[a__]->tp[a]],{elem,states}]]],0];
rules=Solve[Table[Coefficient[ExpandAll[expr]-Sum[b[i]*states[[i]],{i,len}],coefficient]==0,{coefficient,coefficientList}],Table[b[i],{i,len}]];
If[Length[rules]==0,Message[toDDF::nddfState];expr,
ddfStates=ddfStatesList[level,mode,weight];
Sum[b[i]*ddfStates[[i]],{i,len}]/.rules[[1]]],
Message[toDDF::nfile,level,mode,weight];
expr
]]]


(* ::Text:: *)
(*Specify the error messages.*)


(* ::Input::Initialization:: *)
toDDF::lvl= "toDDF does not work on level 1 expressions.";


(* ::Input::Initialization:: *)
toDDF::nfile= "The DDF states for level `1`, mode `2` and weight `3` were not found in the database.";


(* ::Input::Initialization:: *)
toDDF::nddfState= "The expression is not an element of the DDF algebra.";
