(* ::Package:: *)

(* ::Title:: *)
(*Operator Actions*)


(* ::Text:: *)
(*This file is part of the DDF Mathematica Package.*)


(* ::Text:: *)
(*Copyright \[Copyright] 2025 Hannes Malcha*)


(* ::Text:: *)
(*The DDF Package is free software: you can redistribute it and/or modify it under the terms of the GNU General Public License as published by the Free Software Foundation, either version 3 of the License, or (at your option) any later version.*)
(*The DDF Package is distributed in the hope that it will be useful, but WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the GNU General Public License for more details.*)
(*You should have received a copy of the GNU General Public License along with the DDF Package. If not, see https://www.gnu.org/licenses/.*)


(* ::Text:: *)
(*There are a number of operators acting on DDF states and tensor products of DDF states. *)
(*Namely these are the affine generators E, F and H, the Sugawara operator and the coset Virasoro operator.*)
(*This module introduces all these functions.*)


(* ::Section:: *)
(*Public Functions from this Module*)


(* ::Text:: *)
(*rank*)
(*linearIndependenQ*)
(*affineE*)
(*affineF*)
(*affineH*)
(*sugawaraOp*)
(*cosetVirasoroOp*)


(* ::Chapter:: *)
(*Auxiliary Functions*)


(* ::Text:: *)
(*First we give a number of auxiliary functions that are used by all the operators.*)


(* ::Section:: *)
(*Mode Sum*)


(* ::Text:: *)
(*Return the mode sum of a ddfProd or a tp.*)


(* ::Input::Initialization:: *)
modeNumber[A[level_,m_]]:=-m
modeNumber[B[level_,m_]]:=-m
modeNumber[r[m_]]:=-m
modeNumber[d[m_]]:=-m
modeNumber[s[m_]]:=-m


(* ::Input::Initialization:: *)
modeSum[ddfProd[ls_,a_]]:=Sum[modeNumber[elem],{elem,ls}]
modeSum[tp[prod[ls_],a_]]:=Sum[modeNumber[elem],{elem,ls}]


(* ::Section:: *)
(*Tensor Product Investigator*)


(* ::Text:: *)
(*Return the level, modeSum, weight and depth of a tp.*)
(*tpInvestigator assumes that all tp in a Fock state. Hence it only picks one term from a linear combination of tp.*)


(* ::Input::Initialization:: *)
tpInvestigator[Plus[a_,b_]]:=tpInvestigator[a]
tpInvestigator[Times[a_, Plus[b_,c_]]]:=tpInvestigator[a*c]
tpInvestigator[n_*tp[a_,b_]]:=tpInvestigator[tp[a,b]]
tpInvestigator[n_*exp[t_]]:=tpInvestigator[exp[t]]


(* ::Input::Initialization:: *)
tpInvestigator[0]={0,0,0,0};


(* ::Text::Bold:: *)
(*Return: {LEVEL, MODE, WEIGHT, DEPTH}*)


(* ::Input::Initialization:: *)
tpInvestigator[tp[ls_,exp[t_]]]:=Block[{level=sp[d,Expand[t]],mode=modeSum[tp[ls,exp[t]]],weigth=1/2sp[s,Expand[t]]},{level,mode,weigth,level+(weigth^2-1+mode)/level}]


(* ::Input::Initialization:: *)
tpInvestigator[exp[t_]]:=Block[{level=sp[d,Expand[t]],weigth=1/2sp[s,Expand[t]]},{level,0,weigth,level+(weigth^2-1)/level}]


(* ::Section:: *)
(*DDF Product Investigator*)


(* ::Text:: *)
(*Return the level, modeSum, weight and depth of a ddfProd.*)
(*ddfProdInvestigator assumes that all ddfProd in a DDF state have the same properties. Hence it only picks one term from a linear combination of ddfProd.*)


(* ::Input::Initialization:: *)
ddfProdInvestigator[Plus[a_,b_]]:=ddfProdInvestigator[a]
ddfProdInvestigator[Times[a_, Plus[b_,c_]]]:=ddfProdInvestigator[a*c]
ddfProdInvestigator[n_*ddfProd[a_,b_]]:=ddfProdInvestigator[ddfProd[a,b]]
ddfProdInvestigator[n_*exp[t_]]:=ddfProdInvestigator[exp[Expand[t]]]


(* ::Text::Bold:: *)
(*Return: {LEVEL, MODE, WEIGHT, DEPTH}*)


(* ::Input::Initialization:: *)
ddfProdInvestigator[ddfProd[ls_,exp[t_]]]:=Block[{level=sp[d,Expand[t]],mode=modeSum[ddfProd[ls,exp[t]]],weigth=1/2sp[s,Expand[t]]},{level,mode,weigth,level+(weigth^2-1+mode)/level}]


(* ::Input::Initialization:: *)
ddfProdInvestigator[exp[t_]]:=Block[{level=sp[d,Expand[t]],weigth=1/2sp[s,Expand[t]]},{level,0,weigth,level+(weigth^2-1)/level}]


(* ::Text:: *)
(*Tensor products of DDF states are treated as a single DDF state by ddfProdInvestigator and the properties of the tensor factors are summed up.*)


(* ::Input::Initialization:: *)
ddfProdInvestigator[n_*ddfTp[a_,b_]]:=ddfProdInvestigator[ddfTp[a,b]]


(* ::Input::Initialization:: *)
ddfProdInvestigator[ddfTp[a_,b_]]:=ddfProdInvestigator[a]+ddfProdInvestigator[b]


(* ::Section:: *)
(*DDF Tensor Product Investigator*)


(* ::Text:: *)
(*In some cases we need the level, modeSum, weight and depth for each of the factors in a tensor product of DDF states.*)
(*For this there is the function ddfTpInvestigator.*)


(* ::Input::Initialization:: *)
ddfTpInvestigator[Plus[a_,b_]]:=ddfTpInvestigator[a]
ddfTpInvestigator[Times[a_, Plus[b_,c_]]]:=ddfTpInvestigator[a*c]


(* ::Input::Initialization:: *)
ddfTpInvestigator[n_*ddfTp[a_,b_]]:={ddfProdInvestigator[a],ddfProdInvestigator[b]}


(* ::Input::Initialization:: *)
ddfTpInvestigator[ddfTp[a_,b_]]:={ddfProdInvestigator[a],ddfProdInvestigator[b]}


(* ::Section:: *)
(*Linear Independence and Rank*)


(* ::Text:: *)
(*Compute the rank, i.e. the number of linearly independent elements, from a list of ddfProd, ddfTp or tp.*)


(* ::Input::Initialization:: *)
rank[ls_]:=Block[{},coefficientList=DeleteCases[DeleteDuplicates[Flatten[Table[ReplaceAll[If[Head[elem]===Plus,Apply[List,elem],elem],{n_*ddfProd[expr__]->ddfProd[expr],n_*ddfTp[expr__]->ddfTp[expr],n_*tp[expr__]->tp[expr],n_*exp[expr_]->exp[expr]}],{elem,ls}]]],0];MatrixRank[Table[Table[Coefficient[elem,coefficient],{coefficient,coefficientList}],{elem,ls}]]]


(* ::Text:: *)
(*Return true if all elements in a list of ddfProd, ddfTp or tp are linearly independent.*)


(* ::Input::Initialization:: *)
linearIndependenQ[ls_]:=Block[{},If[rank[ls]==Length[ls],True,False]]


(* ::Section:: *)
(*Transform Product of auxA to ddfProdHold*)


(* ::Text:: *)
(*In the definitions of the affine generators and the Sugawara operators we introduce auxiliary transversal DDF operators auxA as well as the auxiliary version of the operator Q. *)
(*A the end of the calculation the product of several auxA[l,n] functions is converted into a formal ddfProdHold that is then joined with the ddfProd on which the operator acts.*)
(*This transformation is done recursively by the function transformAuxA.*)


(* ::Text:: *)
(*Make transformAuxA linear.*)


(* ::Input::Initialization:: *)
transformAuxA[0,ls_]:=0
transformAuxA[Plus[f_,g_],ls_]:=transformAuxA[f,ls]+transformAuxA[g,ls]
transformAuxA[Times[f_,Plus[g_,h_]],ls_]:=transformAuxA[f*g,ls]+transformAuxA[f*h,ls]


(* ::Text:: *)
(*Give recursive definition.*)


(* ::Input::Initialization:: *)
transformAuxA[f_*auxA[a_,b_],ls_]:=transformAuxA[f,Append[ls,A[a,b]]]


(* ::Input::Initialization:: *)
transformAuxA[f_*auxA[a_,b_]^n_,ls_]:=transformAuxA[f,Flatten[Append[ls,Table[A[a,b],n]]]]


(* ::Input::Initialization:: *)
transformAuxA[auxA[a_,b_],ls_]:=transformAuxA[1,Append[ls,A[a,b]]]


(* ::Input::Initialization:: *)
transformAuxA[auxA[a_,b_]^n_,ls_]:=transformAuxA[1,Flatten[Append[ls,Table[A[a,b],n]]]]


(* ::Text:: *)
(*Action on auxQ*)


(* ::Input::Initialization:: *)
transformAuxA[f_*auxQ[n_],ls_]:=f*ddfProdHold[Prepend[Sort[ls],Q[n]]]/;FreeQ[f,auxA[__]]


(* ::Input::Initialization:: *)
transformAuxA[auxQ[n_],ls_]:=ddfProdHold[Prepend[Sort[ls],Q[n]]]


(* ::Text:: *)
(*Exit the recursion*)


(* ::Input::Initialization:: *)
transformAuxA[f_,ls_]:=f*ddfProdHold[Sort[ls]]/;FreeQ[f,auxA[__]]&&FreeQ[f,auxQ[_]]


(* ::Section:: *)
(*Schur Polynomials*)


(* ::Text:: *)
(*There are two kinds of Schur polynomials. One for the affine generators and one for the Sugawara operator.*)


(* ::Subsection:: *)
(*Affine Schur Polynomials*)


(* ::Text:: *)
(*Define the Schur polynomials used in the definitions of the affine generators.*)
(*The lower orders are provided explicitly. The next few orders are read from a database. And the even higher orders are computed at runtime.*)


(* ::Input::Initialization:: *)
affineSchurEval[0,level_,sgn_]:=1


(* ::Input::Initialization:: *)
affineSchurEval[1,level_,sgn_]:=Sqrt[2] sgn auxA[level,-1]


(* ::Input::Initialization:: *)
affineSchurEval[2,level_,sgn_]:=(sgn auxA[level,-2])/Sqrt[2]+auxA[level,-1]^2


(* ::Input::Initialization:: *)
affineSchurEval[3,level_,sgn_]:=1/3 Sqrt[2] sgn auxA[level,-3]+auxA[level,-2] auxA[level,-1]+1/3 Sqrt[2] sgn auxA[level,-1]^3


(* ::Input::Initialization:: *)
affineSchurEval[4,level_,sgn_]:=(sgn auxA[level,-4])/(2 Sqrt[2])+1/4 auxA[level,-2]^2+2/3 auxA[level,-3] auxA[level,-1]+(sgn auxA[level,-2] auxA[level,-1]^2)/Sqrt[2]+1/6 auxA[level,-1]^4


(* ::Input::Initialization:: *)
Get[FileNameJoin[{PackageBaseDirectory,"src", "schur_polynomials","affine_schur_5.wls"}]]


(* ::Input::Initialization:: *)
Get[FileNameJoin[{PackageBaseDirectory,"src", "schur_polynomials","affine_schur_6.wls"}]]


(* ::Input::Initialization:: *)
Get[FileNameJoin[{PackageBaseDirectory,"src", "schur_polynomials","affine_schur_7.wls"}]]


(* ::Input::Initialization:: *)
Get[FileNameJoin[{PackageBaseDirectory,"src", "schur_polynomials","affine_schur_8.wls"}]]


(* ::Input::Initialization:: *)
Get[FileNameJoin[{PackageBaseDirectory,"src", "schur_polynomials","affine_schur_9.wls"}]]


(* ::Input::Initialization:: *)
Get[FileNameJoin[{PackageBaseDirectory,"src", "schur_polynomials","affine_schur_10.wls"}]]


(* ::Input::Initialization:: *)
Get[FileNameJoin[{PackageBaseDirectory,"src", "schur_polynomials","affine_schur_11.wls"}]]


(* ::Input::Initialization:: *)
Get[FileNameJoin[{PackageBaseDirectory,"src", "schur_polynomials","affine_schur_12.wls"}]]


(* ::Text:: *)
(*For n > 12 the Schur polynomials have not been pre-computed. The following function will compute them at runtime and issue a warning that this might delay the evaluation.*)


(* ::Input::Initialization:: *)
affineSchurEval[n_,level_,sgn_]:=Block[{},Message[affineSchurEval::nnarg];
ExpandAll[SeriesCoefficient[Series[Exp[Sum[sgn/j*(Sqrt[2]auxA[level,-j])*z^j,{j,1,n}]],{z,0,n}],n]]]


(* ::Input::Initialization:: *)
affineSchurEval::nnarg= "The Schur polynomial necessary for this calculation has not been pre-computed. Switching to manual evaluation. This might increase the calculation time.";


(* ::Subsection:: *)
(*Sugawara Schur Polynomials*)


(* ::Text:: *)
(*Define the Schur polynomials sugawaraSchurEval used in the definition of the Sugawara operator.*)
(*The lower orders are provided explicitly. The next few orders are read from a database. And the even higher orders are computed at runtime.*)


(* ::Input::Initialization:: *)
sugawaraSchurEval[0,level_,p_,sgn_]:=1


(* ::Input::Initialization:: *)
sugawaraSchurEval[1,level_,p_,sgn_]:=Sqrt[2] sgn auxA[level,-1]-Sqrt[2] sgn auxA[level,-1] unitRoot[level,p]


(* ::Input::Initialization:: *)
sugawaraSchurEval[2,level_,p_,sgn_]:=(sgn auxA[level,-2])/Sqrt[2]+auxA[level,-1]^2-2 auxA[level,-1]^2 unitRoot[level,p]-(sgn auxA[level,-2] unitRoot[level,p]^2)/Sqrt[2]+auxA[level,-1]^2 unitRoot[level,p]^2


(* ::Input::Initialization:: *)
Get[FileNameJoin[{PackageBaseDirectory,"src", "schur_polynomials","sugawara_schur_3.wls"}]]


(* ::Input::Initialization:: *)
Get[FileNameJoin[{PackageBaseDirectory,"src", "schur_polynomials","sugawara_schur_4.wls"}]]


(* ::Input::Initialization:: *)
Get[FileNameJoin[{PackageBaseDirectory , "src", "schur_polynomials","sugawara_schur_5.wls"}]]


(* ::Input::Initialization:: *)
Get[FileNameJoin[{PackageBaseDirectory,"src", "schur_polynomials","sugawara_schur_6.wls"}]]


(* ::Input::Initialization:: *)
Get[FileNameJoin[{PackageBaseDirectory,"src", "schur_polynomials","sugawara_schur_7.wls"}]]


(* ::Input::Initialization:: *)
Get[FileNameJoin[{PackageBaseDirectory,"src", "schur_polynomials","sugawara_schur_8.wls"}]]


(* ::Input::Initialization:: *)
Get[FileNameJoin[{PackageBaseDirectory,"src", "schur_polynomials","sugawara_schur_9.wls"}]]


(* ::Input::Initialization:: *)
Get[FileNameJoin[{PackageBaseDirectory,"src", "schur_polynomials","sugawara_schur_10.wls"}]]


(* ::Text:: *)
(*For n > 10 the Schur polynomials are calculated at runtime.*)


(* ::Input::Initialization:: *)
sugawaraSchurEval[n_,level_,p_,sgn_]:=Block[{},Message[sugawaraSchurEval::nnarg];
ExpandAll[SeriesCoefficient[Series[Exp[Sum[sgn/j*(Sqrt[2]auxA[level,-j](1-Power[unitRoot[level,p],j]))*z^j,{j,1,n}]],{z,0,n}],n]]]/;n>10


(* ::Input::Initialization:: *)
sugawaraSchurEval::nnarg= "The Schur polynomial necessary for this calculation has not been pre-computed. Switching to manual evaluation. This might increase the calculation time.";


(* ::Chapter:: *)
(*Affine Generators*)


(* ::Text:: *)
(*The first kind of operators we introduce are the affine generators E, F, and H.*)
(*The definition of these operators depends on the level of the state on which they act. The level is computed automatically by the generators.*)
(*The generators each take one argument the mode number.*)


(* ::Section:: *)
(*Affine Generators*)


(* ::Text:: *)
(*Functional definitions of the affine generators.*)


(* ::Input::Initialization:: *)
affineE[m_]:=Function[Block[{expr=Expand[#]},affineActionE[m,expr]]]


(* ::Input::Initialization:: *)
affineF[m_]:=Function[Block[{expr=Expand[#]},affineActionF[m,expr]]]


(* ::Input::Initialization:: *)
affineH[m_]:=Function[Block[{expr=Expand[#]},affineActionH[m,expr]]]


(* ::Section:: *)
(*Affine Actions*)


(* ::Text:: *)
(*H*)


(* ::Input::Initialization:: *)
affineActionH[m_,Plus[state1_,state2_]]:=affineActionH[m,state1]+affineActionH[m,state2]


(* ::Input::Initialization:: *)
affineActionH[m_,num_*ddfProd[ddf_,tachyon_]]:=num*affineActionH[m,ddfProd[ddf,tachyon]]


(* ::Input::Initialization:: *)
affineActionH[m_,num_*ddfTp[ddf1_,ddf2_]]:=num*affineActionH[m,ddfTp[ddf1,ddf2]]


(* ::Input::Initialization:: *)
affineActionH[m_,eps[a_,b_]*state_]:=eps[a,b]*affineActionH[m,state]


(* ::Input::Initialization:: *)
affineActionH[m_,exp[tachyon_]]:=affineActionH[m,ddfProd[{},exp[tachyon]]]


(* ::Input::Initialization:: *)
affineActionH[m_,n_*exp[tachyon_]]:=n*affineActionH[m,ddfProd[{},exp[tachyon]]]


(* ::Text:: *)
(*The action on a tensor product is distributively*)


(* ::Input::Initialization:: *)
affineActionH[m_,ddfTp[ddf1_,ddf2_]]:=ddfTp[affineActionH[m,ddf1],ddf2]+ddfTp[ddf1,affineActionH[m,ddf2]]


(* ::Text:: *)
(*The trivial action*)


(* ::Input::Initialization:: *)
affineActionH[m_,0]:=0


(* ::Text:: *)
(*H_m = sqrt(2) * l * A_(l*m).*)


(* ::Input::Initialization:: *)
affineActionH[m_,ddfProd[ddf_,tachyon_]]:=Block[{level=ddfProdInvestigator[ddfProd[ddf,tachyon]][[1]]},Sqrt[2]*joinProd[ddfProdHold[{A[level,level*m]}],ddfProd[ddf,tachyon]]]


(* ::Text:: *)
(*E*)


(* ::Input::Initialization:: *)
affineActionE[m_,Plus[state1_,state2_]]:=affineActionE[m,state1]+affineActionE[m,state2]


(* ::Input::Initialization:: *)
affineActionE[m_,num_*ddfProd[ddf_,tachyon_]]:=num*affineActionE[m,ddfProd[ddf,tachyon]]


(* ::Input::Initialization:: *)
affineActionE[m_,num_*ddfTp[ddf1_,ddf2_]]:=num*affineActionE[m,ddfTp[ddf1,ddf2]]


(* ::Input::Initialization:: *)
affineActionE[m_,eps[a_,b_]*state_]:=eps[a,b]*affineActionE[m,state]


(* ::Input::Initialization:: *)
affineActionE[m_,exp[tachyon_]]:=affineActionE[m,ddfProd[{},exp[tachyon]]]


(* ::Input::Initialization:: *)
affineActionE[m_,n_*exp[tachyon_]]:=n*affineActionE[m,ddfProd[{},exp[tachyon]]]


(* ::Text:: *)
(*The action on a tensor product is distributively*)


(* ::Input::Initialization:: *)
affineActionE[m_,ddfTp[ddf1_,ddf2_]]:=ddfTp[affineActionE[m,ddf1],ddf2]+ddfTp[ddf1,affineActionE[m,ddf2]]


(* ::Text:: *)
(*The trivial action*)


(* ::Input::Initialization:: *)
affineActionE[m_,0]:=0


(* ::Text:: *)
(*The precise definition of E_m is taken from page 8 of [2].*)
(*The function expQPexp is defined below.*)


(* ::Input::Initialization:: *)
affineActionE[m_,ddfProd[ddf_,exp[tachyon_]]]:=Block[{ddfProperties=ddfProdInvestigator[ddfProd[ddf,exp[tachyon]]]},Block[{level=ddfProperties[[1]],modeSum=ddfProperties[[2]]},eps[s,tachyon-modeSum/level*d] joinProd[transformAuxA[ReplaceAll[expQPexp[level,m,modeSum,1,exp[tachyon]], affineSchur->affineSchurEval],{}],ddfProd[ddf,exp[tachyon]]]]]


(* ::Text:: *)
(*F*)


(* ::Input::Initialization:: *)
affineActionF[m_,Plus[state1_,state2_]]:=affineActionF[m,state1]+affineActionF[m,state2]


(* ::Input::Initialization:: *)
affineActionF[m_,num_*ddfProd[ddf_,tachyon_]]:=num*affineActionF[m,ddfProd[ddf,tachyon]]


(* ::Input::Initialization:: *)
affineActionF[m_,num_*ddfTp[ddf1_,ddf2_]]:=num*affineActionF[m,ddfTp[ddf1,ddf2]]


(* ::Input::Initialization:: *)
affineActionF[m_,eps[a_,b_]*state_]:=eps[a,b]*affineActionF[m,state]


(* ::Input::Initialization:: *)
affineActionF[m_,exp[tachyon_]]:=affineActionF[m,ddfProd[{},exp[tachyon]]]


(* ::Input::Initialization:: *)
affineActionF[m_,n_*exp[tachyon_]]:=n*affineActionF[m,ddfProd[{},exp[tachyon]]]


(* ::Text:: *)
(*The action on a tensor product is distributively*)


(* ::Input::Initialization:: *)
affineActionF[m_,ddfTp[ddf1_,ddf2_]]:=ddfTp[affineActionF[m,ddf1],ddf2]+ddfTp[ddf1,affineActionF[m,ddf2]]


(* ::Text:: *)
(*The trivial action*)


(* ::Input::Initialization:: *)
affineActionF[m_,0]:=0


(* ::Text:: *)
(*The  precise  definition  of  F_m  is  taken from page 8 of [2] .*)
(*The function expQPexp is defined below.*)


(* ::Input::Initialization:: *)
affineActionF[m_,ddfProd[ddf_,exp[tachyon_]]]:=Block[{ddfProperties=ddfProdInvestigator[ddfProd[ddf,exp[tachyon]]]},Block[{level=ddfProperties[[1]],modeSum=ddfProperties[[2]]},-eps[-s,tachyon-modeSum/level*d]joinProd[transformAuxA[ReplaceAll[expQPexp[level,m,modeSum,-1,exp[tachyon]],affineSchur->affineSchurEval],{}],ddfProd[ddf,exp[tachyon]]]]]


(* ::Subsection:: *)
(*Helper Function*)


(* ::Text:: *)
(*The exponential function used in E_m and F_m is defined as follows*)


(* ::Input::Initialization:: *)
expQPexp[level_, m_, mode_, sgn_, exp[state_]] := auxQ[sgn]*Coefficient[Sum[affineSchur[k, level, sgn]*z^k, {k, 0, 20}]*(1 + Sum[1/k!*Sum[Coefficient[Sum[-sgn/n*(Sqrt[2]*auxA[level, n]*y^n)*z^(-n), {n, 1, mode}]^k, y, i], {i, 0, mode}], {k, 1, mode}]), z, Expand[-1-level*m-sgn*sp[s, state]]]


(* ::Chapter:: *)
(*Sugawara Operator*)


(* ::Text:: *)
(*Next we define the Sugawara operator.*)
(*The definition of the Sugawara operators depends on the level of the state on which it acts . The level is computed automatically by the operator .*)
(*Also the Sugawara operator takes a mode number as an argument.*)


(* ::Section:: *)
(*Sugawara Operator*)


(* ::Text:: *)
(*Functional definition of the Sugawara operator.*)


(* ::Input::Initialization:: *)
sugawaraOp[m_]:=Function[Block[{expr=Expand[#]},If[expr==0,Return[0,Block]];
Block[{ddfProperties=ddfProdInvestigator[expr]},sugawaraOpAction[ddfProperties[[1]],ddfProperties[[2]],m,expr]]]]


(* ::Section:: *)
(*Sugawara Operator Action*)


(* ::Text:: *)
(*We give the general properties of the action of the Sugawara operator on ddfProd and ddfTp.*)


(* ::Input::Initialization:: *)
sugawaraOpAction[args__,m_,Plus[state1_,state2_]]:=sugawaraOpAction[args,m,state1]+sugawaraOpAction[args,m,state2]
sugawaraOpAction[args__,m_,n_*ddfProd[ddf_,tachyon_]]:=n*sugawaraOpAction[args,m,ddfProd[ddf,tachyon]]
sugawaraOpAction[args__,m_,eps[a_,b_]*state_]:=eps[a,b]*sugawaraOpAction[args,m,state]
sugawaraOpAction[args__,m_,0]:=0


(* ::Text:: *)
(*Define the action on a tachyonic state*)


(* ::Input::Initialization:: *)
sugawaraOpAction[args__,m_,exp[tachyon_]]:=sugawaraOpAction[args,m,ddfProd[{},exp[tachyon]]]
sugawaraOpAction[args__,m_,n_*exp[tachyon_]]:=n*sugawaraOpAction[args,m,ddfProd[{},exp[tachyon]]]


(* ::Subsection:: *)
(*Action on a ddfProd*)


(* ::Text:: *)
(*The action of the Sugawara operator on a ddfProd is given in (3.27) of [2].*)
(*We split the action into four terms and evaluate them separately.*)


(* ::Input::Initialization:: *)
sugawaraOpAction[level_,modeSum_,m_,ddfProd[ddf_,tachyon_]]:=term1[level,m,modeSum,ddfProd[ddf,tachyon]]+term2[level,m,modeSum,ddfProd[ddf,tachyon]]+term3[level,m,modeSum,tachyon,ddfProd[ddf,tachyon]]+term4[level,m,modeSum,tachyon,ddfProd[ddf,tachyon]]


(* ::Text:: *)
(*The four terms are defined as follow:*)
(*1st Term*)
(*The cutoff and normalOrdering functions are defined below*)


(* ::Input::Initialization:: *)
term1[level_,m_,mode_,ddfProd[ddf_,tachyon_]]:=1/(2*level) joinProd[Sum[cutoff[normalOrdering[ddfProdHold[{A[level,level*k],A[level,level(m-k)]}]],mode],{k,-Infinity,Infinity}],ddfProd[ddf,tachyon]]


(* ::Text:: *)
(*2nd Term*)


(* ::Input::Initialization:: *)
term2[1,m_,mode_,ddfProd[ddf_,tachyon_]]:=0


(* ::Input::Initialization:: *)
term2[level_,m_,mode_,ddfProd[ddf_,tachyon_]]:=1/(level(level+2)) joinProd[Sum[(1-KroneckerDelta[0,Mod[k,level]])cutoff[normalOrdering[ddfProdHold[{A[level,k],A[level,level*m-k]}]],mode],{k,-Infinity,Infinity}],ddfProd[ddf,tachyon]]/;level>1


(* ::Text:: *)
(*3rd Term*)


(* ::Input::Initialization:: *)
term3[1,m_,mode_,exp[state_],ddfProd[ddf_,tachyon_]]:=0


(* ::Input::Initialization:: *)
term3[level_,m_,mode_,exp[state_],ddfProd[ddf_,tachyon_]]:=0/;m!=0


(* ::Input::Initialization:: *)
term3[level_,0,mode_,exp[state_],ddfProd[ddf_,tachyon_]]:=((Mod[sp[s,state],level]*(level-Mod[sp[s,state],level]))/(4*level(level+2))+(Mod[sp[-s,state],level]*(level-Mod[sp[-s,state],level]))/(4*level(level+2)))*joinProd[ddfProdHold[{}],ddfProd[ddf,tachyon]]/;level>1


(* ::Text:: *)
(*4th Term*)


(* ::Input::Initialization:: *)
term4[1,m_,mode_,exp[state_],ddfProd[ddf_,tachyon_]]:=0


(* ::Input::Initialization:: *)
term4[level_,m_,mode_,exp[state_],ddfProd[ddf_,tachyon_]]:=joinProd[transformAuxA[ReplaceAll[sumResExp[level,m,mode,-1,exp[state]],sugawaraSchur->sugawaraSchurEval],{}]+transformAuxA[ReplaceAll[sumResExp[level,m,mode,1,exp[state]],sugawaraSchur->sugawaraSchurEval],{}],ddfProd[ddf,tachyon]]/;level>1


(* ::Text:: *)
(*The sumResExp function is*)


(* ::Input::Initialization:: *)
sumResExp[level_, m_, mode_, sgn_, exp[state_]] :=  -(Sum[(unitRoot[level, p]^(-sgn*sp[s, state])*Coefficient[Sum[sugawaraSchur[k,level,p,sgn]*z^k, {k, 0, 100}]*(1 + Sum[Sum[Coefficient[Sum[(-sgn*Sqrt[2]*auxA[level, n]*y^n*(1 - unitRoot[level, p]^(-n)))/(z^n*n), {n, 1, mode}]^k, y, i], {i, 0, mode}]/k!, {k, 1, mode}]) - 1, z, (-level)*m])/
      Abs[unitRoot[level, p] - 1]^2, {p, 1, level - 1}]/(2*level*(level + 2)))


(* ::Text:: *)
(*It uses the self explanatory unitRoot function.*)


(* ::Input::Initialization:: *)
unitRoot[level_,p_]:=Exp[2\[Pi]*I*p/level]


(* ::Subsection:: *)
(*Action on a ddfTp*)


(* ::Text:: *)
(*The action of the Sugawara operator on a tensor product of DDF states is computed through the affine generator representation of the Sugawara operator.*)
(*This way of evaluating the action of the Sugawara operator is slower than the one above, so we only use it when necessary, i.e. when acting on tensor products of DDF states.*)


(* ::Input::Initialization:: *)
sugawaraOpAction[args__,m_,ddfTp[a_,b_]]:=sugawaraOpTpAction[m,ddfTp[a,b]]


(* ::Input::Initialization:: *)
sugawaraOpAction[args__,m_,n_*ddfTp[a_,b_]]:=n*sugawaraOpTpAction[m,ddfTp[a,b]]


(* ::Text:: *)
(*Make the action linear*)


(* ::Input::Initialization:: *)
sugawaraOpTpAction[m_,Plus[state1_,state2_]]:=sugawaraOpTpAction[m,state1]+sugawaraOpTpAction[m,state2]
sugawaraOpTpAction[m_,num_*ddfTp[ddf1_,ddf2_]]:=num*sugawaraOpTpAction[m,ddfTp[ddf1,ddf2]]
sugawaraOpTpAction[m_,eps[a_,b_]*state_]:=eps[a,b]*sugawaraOpTpAction[m,state]
sugawaraOpTpAction[m_,0]:=0


(* ::Text:: *)
(*Give the precise definition according to (3.22) from [2] in terms of affine generators.*)
(*The affineAction function is defined below*)


(* ::Input::Initialization:: *)
sugawaraOpTpAction[m_,ddfTp[ddf1_,ddf2_]]:=Block[{ddfProperties1=ddfProdInvestigator[ddf1],ddfProperties2=ddfProdInvestigator[ddf2]},
Block[{level1=ddfProperties1[[1]],depth1=ddfProperties1[[4]],level2=ddfProperties2[[1]],depth2=ddfProperties2[[4]]}, 1/(4*(level1+level2+2)) affineAction[Sum[cutoff[normalOrdering[affineOps[auxH[k],auxH[m-k]]],depth1,depth2],{k,-Infinity,Infinity}],ddfTp[ddf1,ddf2]]+1/(2*(level1+level2+2)) affineAction[Sum[cutoff[normalOrdering[affineOps[auxE[k],auxF[m-k]]],depth1,depth2],{k,-Infinity,Infinity}],ddfTp[ddf1,ddf2]]+1/(2*(level1+level2+2)) affineAction[Sum[cutoff[normalOrdering[affineOps[auxF[k],auxE[m-k]]],depth1,depth2],{k,-Infinity,Infinity}],ddfTp[ddf1,ddf2]]]]


(* ::Text:: *)
(*Define a special version of sugawaraOpTp where all arguments are provided manually.*)
(*This is useful to speed up the evaluation of the coset Virasoro operator.*)


(* ::Input::Initialization:: *)
sugawaraOpTpActionPrivate[level1_,depth1_,level2_,depth2_,m_,ddfTp[ddf1_,ddf2_]]:=1/(4*(level1+level2+2)) affineAction[Sum[cutoff[normalOrdering[affineOps[auxH[k],auxH[m-k]]],depth1,depth2],{k,-Infinity,Infinity}],ddfTp[ddf1,ddf2]]+1/(2*(level1+level2+2)) affineAction[Sum[cutoff[normalOrdering[affineOps[auxE[k],auxF[m-k]]],depth1,depth2],{k,-Infinity,Infinity}],ddfTp[ddf1,ddf2]]+1/(2*(level1+level2+2)) affineAction[Sum[cutoff[normalOrdering[affineOps[auxF[k],auxE[m-k]]],depth1,depth2],{k,-Infinity,Infinity}],ddfTp[ddf1,ddf2]]


(* ::Subsection:: *)
(*Helper Functions*)


(* ::Text:: *)
(*The auxiliary affine generators are wrapped in a helper function to compute their action on the tensor product of DDF states.*)
(*This is a linear function.*)


(* ::Input::Initialization:: *)
affineOps[Plus[expr1_,expr2_],expr3_]:=affineOps[expr1,expr3]+affineOps[expr2,expr3]
affineOps[expr1_,Plus[expr2_,expr3_]]:=affineOps[expr1,expr2]+affineOps[expr1,expr3]
affineOps[Times[n_*Plus[expr1_,expr2_]],expr3_]:=affineOps[n*expr1,expr3]+affineOps[n*expr2,expr3]
affineOps[expr1_,Times[n_*Plus[expr2_,expr3_]]]:=affineOps[expr1,n*expr2]+affineOps[expr1,n*expr3]


(* ::Input::Initialization:: *)
affineOps[f_*auxH[m_],expr1_]:=f*affineOps[auxH[m],expr1]
affineOps[f_*auxE[m_],expr1_]:=f*affineOps[auxE[m],expr1]
affineOps[f_*auxF[m_],expr1_]:=f*affineOps[auxF[m],expr1]


(* ::Input::Initialization:: *)
affineOps[expr1_,f_*auxH[m_]]:=f*affineOps[expr1,auxH[m]]
affineOps[expr1_,f_*auxE[m_]]:=f*affineOps[expr1,auxE[m]]
affineOps[expr1_,f_*auxF[m_]]:=f*affineOps[expr1,auxF[m]]


(* ::Text:: *)
(*The action of the affine generators on the tensor product of DDF states is then given as follows.*)


(* ::Input::Initialization:: *)
affineAction[0,ddfTp[ddf1_,ddf2_]]:=0
affineAction[Plus[expr1_,expr2_],ddfTp[ddf1_,ddf2_]]:=affineAction[expr1,ddfTp[ddf1,ddf2]]+affineAction[expr2,ddfTp[ddf1,ddf2]]
affineAction[Times[n_*Plus[expr1_,expr2_]],ddfTp[ddf1_,ddf2_]]:=affineAction[n*expr1,ddfTp[ddf1,ddf2]]+affineAction[n*expr2,ddfTp[ddf1,ddf2]]
affineAction[n_*affineOps[expr1_,expr2_],ddfTp[ddf1_,ddf2_]]:=n*affineAction[affineOps[expr1,expr2],ddfTp[ddf1,ddf2]]


(* ::Input::Initialization:: *)
affineAction[affineOps[auxH[m1_],auxH[m2_]],ddfTp[ddf1_,ddf2_]]:=affineH[m1][affineH[m2][ddfTp[ddf1,ddf2]]]
affineAction[affineOps[auxE[m1_],auxF[m2_]],ddfTp[ddf1_,ddf2_]]:=affineE[m1][affineF[m2][ddfTp[ddf1,ddf2]]]
affineAction[affineOps[auxF[m1_],auxE[m2_]],ddfTp[ddf1_,ddf2_]]:=affineF[m1][affineE[m2][ddfTp[ddf1,ddf2]]]


(* ::Text:: *)
(*The normal ordering of a ddfProdHold is defined as*)


(* ::Input::Initialization:: *)
normalOrdering[ddfProdHold[{A[level_,a_],A[level_,b_]}]]:=If[a>b,ddfProdHold[{A[level,b],A[level,a]}],ddfProdHold[{A[level,a],A[level,b]}]]


(* ::Text:: *)
(*The normal ordering of affine generators is defined as*)


(* ::Input::Initialization:: *)
normalOrdering[affineOps[auxH[a_],auxH[b_]]]:=If[a>b,affineOps[auxH[b],auxH[a]],affineOps[auxH[a],auxH[b]]]


(* ::Input::Initialization:: *)
normalOrdering[affineOps[auxE[a_],auxF[b_]]]:=If[a>b,affineOps[auxF[b],auxE[a]],affineOps[auxE[a],auxF[b]]]


(* ::Input::Initialization:: *)
normalOrdering[affineOps[auxF[a_],auxE[b_]]]:=If[a>b,affineOps[auxE[b],auxF[a]],affineOps[auxF[a],auxE[b]]]


(* ::Text:: *)
(*The sum over DDF operators respectively affine generators in the Sugawara operator is formally infinite. However, only finitely many terms give a non-zero contribution to the operator. To extract only those we define a cutoff function.*)


(* ::Input::Initialization:: *)
cutoff[ddfProdHold[{A[level_,a_],A[level_,b_]}],depth_]:=If[b>depth,0,ddfProdHold[{A[level,a],A[level,b]}]]


(* ::Text:: *)
(*Define a cutoff function for  affine generators*)


(* ::Input::Initialization:: *)
cutoff[affineOps[auxH[a_],auxH[b_]],depth1_,depth2_]:=If[And[b>depth1,b>depth2] ,0,affineOps[auxH[a],auxH[b]]]


(* ::Input::Initialization:: *)
cutoff[affineOps[auxE[a_],auxF[b_]],depth1_,depth2_]:=If[And[b>depth1,b>depth2] ,0,affineOps[auxE[a],auxF[b]]]


(* ::Input::Initialization:: *)
cutoff[affineOps[auxF[a_],auxE[b_]],depth1_,depth2_]:=If[And[b>depth1,b>depth2] ,0,affineOps[auxF[a],auxE[b]]]


(* ::Chapter:: *)
(*Coset Virasoro Operator*)


(* ::Text:: *)
(*Then we define the coset Virasoro operator on tensor products of DDF states in terms of the Sugawara operator.*)


(* ::Section:: *)
(*Coset Virasoro Operator*)


(* ::Text:: *)
(*Define the coset Virasoro operator that acts on a ddfTp. It takes the mode as an argument.*)


(* ::Input::Initialization:: *)
cosetVirasoroOp[m_]:=Function[Block[{expr=Expand[#]},cosetVirasoroOpAction[m,expr]]]


(* ::Text:: *)
(*We also define a version of this operator that acts on multiple tensor products of DDF states on a given level.*)


(* ::Input::Initialization:: *)
cosetVirasoroOp[level_,m_]:=Function[cosetVirasoroOpTensorAction[level,m,Expand[#]]]


(* ::Section:: *)
(*Coset Virasoro Operator Action*)


(* ::Input::Initialization:: *)
cosetVirasoroOpAction[m_,Plus[state1_,state2_]]:=cosetVirasoroOpAction[m,state1]+cosetVirasoroOpAction[m,state2]
cosetVirasoroOpAction[m_,num_*ddfTp[ddf1_,ddf2_]]:=num*cosetVirasoroOpAction[m,ddfTp[ddf1,ddf2]]
cosetVirasoroOpAction[m_,eps[a_,b_]*state_]:=eps[a,b]*cosetVirasoroOpAction[m,state]
cosetVirasoroOpAction[m_,0]:=0


(* ::Text:: *)
(*Give the explicit action in terms of the Sugawara operator.*)


(* ::Input::Initialization:: *)
cosetVirasoroOpAction[m_,ddfTp[ddf1_,ddf2_]]:=Block[{ddfProperties1=ddfProdInvestigator[ddf1],ddfProperties2=ddfProdInvestigator[ddf2]},
Block[{level1=ddfProperties1[[1]],modeSum1=ddfProperties1[[2]],depth1=ddfProperties1[[4]],
level2=ddfProperties2[[1]],modeSum2=ddfProperties2[[2]],depth2=ddfProperties2[[4]]},
ddfTp[sugawaraOpAction[level1,modeSum1,m,ddf1],ddf2]+ddfTp[ddf1,sugawaraOpAction[level2,modeSum2,m,ddf2]]-sugawaraOpTpActionPrivate[level1,depth1,level2,depth2,m,ddfTp[ddf1,ddf2]]]]


(* ::Section:: *)
(*Higher Tensor coset Virasoro Operator Action*)


(* ::Input::Initialization:: *)
cosetVirasoroOpTensorAction[level_,m_,Plus[a_,b_]]:=cosetVirasoroOpTensorAction[level,m,a]+cosetVirasoroOpTensorAction[level,m,b]
cosetVirasoroOpTensorAction[level_,m_,Times[a_,Plus[b_,c_]]]:=a*cosetVirasoroOpTensorAction[level,m,b]+a*cosetVirasoroOpTensorAction[level,m,c]
cosetVirasoroOpTensorAction[level_,m_,a_*ddfTp[b__]]:=a*cosetVirasoroOpTensorAction[level,m,ddfTp[b]]
cosetVirasoroOpTensorAction[level_,m_,0]:=0


(* ::Text:: *)
(*Turn a tenor product into a list.*)


(* ::Input::Initialization:: *)
tpToList[ddfTp[a_,b_]]:=Flatten@{a,tpToList[b]}/;Head[b]==ddfTp
tpToList[ddfTp[a_,b_]]:={a,b}


(* ::Text:: *)
(*This function is self descriptive*)


(* ::Input::Initialization:: *)
mapFunction[fun_,{a___,b_,c_}]:={a,fun[b,c]}


(* ::Text:: *)
(*Loop through the nested tensor product and act with the usual coset Virasoro operator at the appropriate level.*)


(* ::Input::Initialization:: *)
cosetVirasoroOpTensorAction[level_,m_,ddfTp[a__]]:=Block[{ddfList=tpToList[ddfTp[a]],n=level-1},
While[n>0,ddfList=mapFunction[ddfTp,ddfList];n--];
ddfList=MapAt[cosetVirasoroOp[m],ddfList,-1];
If[Length[ddfList]==1,ddfList[[1]],Fold[ddfTp[#2,#1]&,Reverse[ddfList]]]
]
