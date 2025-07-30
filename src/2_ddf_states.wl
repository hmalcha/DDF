(* ::Package:: *)

(* ::Title:: *)
(*DDF States*)


(* ::Text:: *)
(*This file is part of the DDF Mathematica Package.*)


(* ::Text:: *)
(*Copyright \[Copyright] 2025 Hannes Malcha*)


(* ::Text:: *)
(*The DDF Package is free software: you can redistribute it and/or modify it under the terms of the GNU General Public License as published by the Free Software Foundation, either version 3 of the License, or (at your option) any later version.*)
(*The DDF Package is distributed in the hope that it will be useful, but WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the GNU General Public License for more details.*)
(*You should have received a copy of the GNU General Public License along with the DDF Package. If not, see https://www.gnu.org/licenses/.*)


(* ::Text:: *)
(*This module introduces DDF states. DDF states are linear combinations of products of DDF operators acting on tachyonic (ground) states.*)


(* ::Text:: *)
(*One such product of DDF operators acting on a tachyonic state is denoted by ddfProd[{...},exp[...]], where the first argument is a list transversal and longitudinal DDF operators A[l,m] and B[l,m], i.e. the product, and the second argument is the tachyonic state.*)


(* ::Text:: *)
(*If the list of DDF operators is not normal ordered or contains annihilation operators ddfProd will automatically order the product and act with the annihilation operators respecting the commutation relations of DDF operators . *)


(* ::Text:: *)
(*This module also introduces the tensor product of DDF states. These are the elements of the tensor algebra.*)


(* ::Text:: *)
(*DDF vertex operators relating DDF states and Fock states are introduced in the ddf_vertex_operators.wl module.*)


(* ::Section:: *)
(*Public Functions from this Module*)


(* ::Text:: *)
(*A*)
(*B*)
(*a*)
(*ddfProd*)
(*ddfTp*)
(*autoCom*)


(* ::Section:: *)
(*Tachyonic Momenta*)


(* ::Text:: *)
(*Tachyonic (ground) states exp[...] have fixed momenta defined in (3.10) of [3].*)


(* ::Input::Initialization:: *)
a[l_,n_]:=-l*r-(l+(n^2-1)/l)d+n*s


(* ::Section:: *)
(*The DDF Product*)


(* ::Text:: *)
(*Make the products of DDF operators linear.*)


(* ::Input::Initialization:: *)
ddfProd[{ls1___,Plus[a_,b_],ls2___},c_]:=ddfProd[{ls1,a,ls2},c]+ddfProd[{ls1,b,ls2},c]


(* ::Input::Initialization:: *)
ddfProd[{ls1___,Times[n_?NumericQ,a_],ls2___},c_]:=n*ddfProd[{ls1,a,ls2},c]


(* ::Input::Initialization:: *)
ddfProd[{ls1___,0,ls2___},c_]:=0


(* ::Text:: *)
(*Define the action of DDF (annihilation) operators inside the ddfProd.*)


(* ::Input::Initialization:: *)
ddfProd[{ls1___,A[level_,m_],A[level_,n_],ls2___},exp[t_]]:=m*KroneckerDelta[0,m+n]*ddfProd[{ls1,ls2},exp[t]]+ddfProd[{ls1,A[level,n],A[level,m],ls2},exp[t]]/;m>n


(* ::Input::Initialization:: *)
ddfProd[{ls1___,B[level_,m_],A[level_,n_],ls2___},exp[t_]]:=-n*ddfProd[{ls1,A[level,m+n],ls2},exp[t]]+n/Sqrt[2]*sp[s,t]*KroneckerDelta[0,m+n]*ddfProd[{ls1,ls2},exp[t]]+ddfProd[{ls1,A[level,n],B[level,m],ls2},exp[t]]/;n<0


(* ::Input::Initialization:: *)
ddfProd[{ls1___,A[level_,m_],B[level_,n_],ls2___},exp[t_]]:=m*ddfProd[{ls1,A[level,m+n],ls2},exp[t]]-m/Sqrt[2]*sp[s,t]*KroneckerDelta[0,m+n]*ddfProd[{ls1,ls2},exp[t]]+ddfProd[{ls1,B[level,n],A[level,m],ls2},exp[t]]/;m>=0


(* ::Input::Initialization:: *)
ddfProd[{ls1___,A[level_,m_]},exp[t_]]:=0/;m>0


(* ::Input::Initialization:: *)
ddfProd[{ls1___,A[level_,0]},exp[t_]]:=sp[s,t]/Sqrt[2]*ddfProd[{ls1},exp[t]]


(* ::Text:: *)
(*Define the action of the operator Q inside the ddfProd*)


(* ::Input::Initialization:: *)
ddfProd[{ls1___,Q[m_],A[level_,n_],ls2___},exp[t_]]:=ddfProd[{ls1,A[level,n],Q[m],ls2},exp[t]]/;n<0


(* ::Input::Initialization:: *)
ddfProd[{ls1___,Q[m_],B[level_,n_],ls2___},exp[t_]]:=ddfProd[{ls1,B[level,n],Q[m],ls2},exp[t]]/;n<0


(* ::Input::Initialization:: *)
ddfProd[{ls1___,Q[n_]},exp[t_]]:=ddfProd[{ls1},exp[a[sp[d,t],sp[s,t]/2+n]]]


(* ::Section:: *)
(*Join DDF Products*)


(* ::Text:: *)
(*Affine generators and the Sugawara operator act on DDF products by multiplication from the left.*)
(*We implement this by defining the functions ddfProdHold and joinProd.*)


(* ::Text:: *)
(*ddfProdHold is a linear function that keeps a product of DDF operators in an unevaluated form.*)


(* ::Input::Initialization:: *)
ddfProdHold[{ls1___,Plus[a_,b_],ls2___}]:=ddfProdHold[{ls1,a,ls2}]+ddfProdHold[{ls1,b,ls2}]


(* ::Input::Initialization:: *)
ddfProdHold[{ls1___,Times[n_?NumericQ,a_],ls2___}]:=n*ddfProdHold[{ls1,a,ls2}]


(* ::Input::Initialization:: *)
ddfProdHold[{ls1___,0,ls2___}]:=0


(* ::Text:: *)
(*joinProd takes a ddfProd and a ddfProdHold and joins them together.*)


(* ::Text:: *)
(*Make joinProd linear*)


(* ::Input::Initialization:: *)
joinProd[0,b_]:=0


(* ::Input::Initialization:: *)
joinProd[n_?NumericQ*a_,b_]:=n*joinProd[a,b]


(* ::Input::Initialization:: *)
joinProd[a_,n_?NumericQ*b_]:=n*joinProd[a,b]


(* ::Input::Initialization:: *)
joinProd[f_,eps[a_,b_]*g_]:=eps[a,b]*joinProd[f,g]


(* ::Input::Initialization:: *)
joinProd[Times[n_,Plus[a_,b_],c_]]:=joinProd[n*a,c]+joinProd[n*b,c]


(* ::Input::Initialization:: *)
joinProd[Plus[a_,b_],c_]:=joinProd[a,c]+joinProd[b,c]


(* ::Input::Initialization:: *)
joinProd[a_,Plus[b_,c_]]:=joinProd[a,b]+joinProd[a,c]


(* ::Text:: *)
(*Define the joining.*)


(* ::Input::Initialization:: *)
joinProd[ddfProdHold[a_],ddfProd[b_,c_]]:=ddfProd[Join[a,b],c]


(* ::Section:: *)
(*DDF Tensor Product*)


(* ::Text:: *)
(*Define the tensor product of two DDF states.*)
(*Note that the tensor product can be nested, i.e. its elements can be tensor products themselves.*)


(* ::Input::Initialization:: *)
ddfTp[_,0]:=0
ddfTp[0,_]:=0


(* ::Input::Initialization:: *)
ddfTp[Plus[a_,b_],c_]:=ddfTp[a,c]+ddfTp[b,c]
ddfTp[a_,Plus[b_,c_]]:=ddfTp[a,b]+ddfTp[a,c]


(* ::Input::Initialization:: *)
ddfTp[Times[a_,Plus[b_,c_]],d_]:=ddfTp[a*b,d]+ddfTp[a*c,d]
ddfTp[a_,Times[b_,Plus[c_,d_]]]:=ddfTp[a,b*c]+ddfTp[a,b*d]


(* ::Input::Initialization:: *)
ddfTp[a_*ddfProd[b__],c_]:=a*ddfTp[ddfProd[b],c]
ddfTp[a_,b_*ddfProd[c__]]:=b*ddfTp[a,ddfProd[c]]


(* ::Input::Initialization:: *)
ddfTp[a_*exp[b_],c_]:=a*ddfTp[exp[b],c]
ddfTp[a_,b_*exp[c_]]:=b*ddfTp[a,exp[c]]


(* ::Input::Initialization:: *)
ddfTp[a_*ddfTp[b__],c_]:=a*ddfTp[ddfTp[b],c]
ddfTp[a_,b_*ddfTp[c__]]:=b*ddfTp[a,ddfTp[c]]


(* ::Input::Initialization:: *)
ddfTp[a_,ddfProd[{},exp[t_]]]:=ddfTp[a,exp[t]]
ddfTp[ddfProd[{},exp[t_]],a_]:=ddfTp[exp[t],a]


(* ::Text:: *)
(*Replace a DDF tensor product by a commutator and compute the resulting DDF state.*)


(* ::Text:: *)
(*We introduce an auxiliary function that replaces only the innermost ddfTp by com*)


(* ::Input::Initialization:: *)
iterativeCom[f_+g_]:=iterativeCom[f]+iterativeCom[g]
iterativeCom[f_*ddfTp[a_,b_]]:=f*iterativeCom[ddfTp[a,b]]


(* ::Input::Initialization:: *)
iterativeCom[ddfTp[a_,b_]]:=Block[{comExpr,sortExpr},
If[FreeQ[b,ddfTp],
comExpr=com[a,b];
sortExpr=sortProd[comExpr];
Quiet[ReplaceAll[toDDF[Expand[sortExpr]],B[_,-1]->0]],
ddfTp[a,iterativeCom[b]]]]


(* ::Text:: *)
(*Then we can define the main function. If there are too many terms we choose to parallelize the action. The cutoff for parallelization is chosen quite high because of the large overhead it causes.*)


(* ::Input::Initialization:: *)
autoCom=Function[Module[{expr=Expand[#],result},
If[FreeQ[expr,ddfTp],Return[expr,Module]];
If[Head[expr]===Plus&&Length[expr]>50,autoComList[List@@expr]];
result=iterativeCom[expr];
autoCom[result]]];


(* ::Text:: *)
(*The parallel action is defined as follows*)


(* ::Input::Initialization:: *)
autoComList[ls_]:=Module[{comExpr,sortExpr,result},
result=Expand[Total[ParallelMap[iterativeCom,ls]]];
autoCom[result]]
