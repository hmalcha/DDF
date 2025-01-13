(* ::Package:: *)

(* ::Title:: *)
(*DDF Construction of F*)


(* ::Text:: *)
(*This is the DDF package. It facilitates the DDF construction of the root spaces of the Feingold-Frenkel algebra F, a hyperbolic Kac-Moody algebra. *)
(*The package handles the calculation of DDF states and their commutators. *)
(*Moreover, it computes the action of affine generators and the Sugawara operator on DDF states at any level*)


(* ::Text:: *)
(*The  functions  used  in  this  package  are  derived  from  the  papers [1, 2] and  appropriately  adjusted  to  the  Feingold-Frenkel  algebra  F .*)


(* ::Text:: *)
(*[1] R.W. Gebert and H. Nicolai, On E(10) and the DDF construction, Commun. Math. Phys. 172 (1995), 571-622, arXiv:hep-th/9406175.*)


(* ::Text:: *)
(*[2] R.W. Gebert and H. Nicolai, An Affine string vertex operator construction at arbitrary level, J. Math. Phys. 38 (1997), 4435-4450, arXiv:hep-th/9608014.*)


(* ::Text:: *)
(*The DDF package has been used to to obtain the result presented in*)


(* ::Text:: *)
(*[3] S . Capolongo, A . Kleinschmidt, H . Malcha and H . Nicolai, "A string-like realization of hyperbolic Kac-Moody algebras", arXiv : 2411.18754 [hep-th] .*)


(* ::Text:: *)
(*This file is part of the DDF Package for Mathematica.*)
(*The DDF Package is free software: you can redistribute it and/or modify it under the terms of the GNU General Public License as published by the Free Software Foundation, either version 3 of the License, or (at your option) any later version.*)
(*The DDF Package is distributed in the hope that it will be useful, but WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the GNU General Public License for more details.*)
(*You should have received a copy of the GNU General Public License along with the DDF Package. If not, see https://www.gnu.org/licenses/.*)


(* ::Text:: *)
(*Copyright \[Copyright] 2025*)
(*Hannes Malcha*)
(*hannes.malcha@aei.mpg.de*)


(* ::Section:: *)
(*Begin Package*)


(* ::Input::Initialization:: *)
BeginPackage["ddf`"]


(* ::Input::Initialization:: *)
Unprotect["ddf`*"];


(* ::Section:: *)
(*Symbol and Function Definitions*)


(* ::Subsection:: *)
(*Symbols*)


(* ::Input::Initialization:: *)
r::usage="Simple root \!\(\*SubscriptBox[\(r\), \(-1\)]\).";


(* ::Input::Initialization:: *)
d::usage="Affine null root \[Delta] = \!\(\*SubscriptBox[\(r\), \(0\(\\\ \)\)]\)+ \!\(\*SubscriptBox[\(r\), \(1\)]\).";


(* ::Input::Initialization:: *)
s::usage="Simple root \!\(\*SubscriptBox[\(r\), \(1\)]\)";


(* ::Input::Initialization:: *)
cartanMatrix::usage="The Catan matrix of F";


(* ::Subsection:: *)
(*Functions*)


(* ::Input::Initialization:: *)
sp::usage="sp[linCombo_roots_1,linCombo_roots_2] computes the scalar product of roots according to the Cartan matrix. Expects two arguments which are linear combinations of roots. Returns a number.";


(* ::Input::Initialization:: *)
A::usage="A[l,m] is the transversal DDF operator of level l and mode m. A[l,m] is used in the first argument of ddfProd.";


(* ::Input::Initialization:: *)
B::usage="B[l,m] is the longitudinal DDF operator of level l and mode m. B[l,m] is used in the first argument of ddfProd.";


(* ::Input::Initialization:: *)
opA::usage="opA[l,m][state] is the transversal DDF operator of level l and mode m. It acts on other DDF operators (opA or opB) or tachionic states (exp[limCombo_roots]). Returns the resulting state as a Fock space element (see also tp).";


(* ::Input::Initialization:: *)
opB::usage="opB[l,m][state] is the longitudinal DDF operator of level l and mode m. It acts on other DDF operators (opA or opB) or tachionic states (exp[limCombo_roots]). Returns the resulting state as a Fock space element (see also tp).";


(* ::Input::Initialization:: *)
exp::usage="exp[limCombo_roots] defines the tachionic states that span the twisted group algebra \!\(\*TemplateBox[{},\n\"Reals\"]\){\[CapitalLambda]}. Used in the second argument of tp and ddfProd or as the argument of opA and opB.";


(* ::Input::Initialization:: *)
prod::usage="prod[{list_roots}] is a product of roots \!\(\*SubscriptBox[\(u\), \(i\)]\)[m] \[Element] \!\(\*SubscriptBox[\(\[CapitalLambda]\), \(\[DoubleStruckCapitalR]\)]\), where \!\(\*SubscriptBox[\(\[CapitalLambda]\), \(\[DoubleStruckCapitalR]\)]\) = \[DoubleStruckCapitalR] \[CircleTimes] \[CapitalLambda] is the vector space of roots and \!\(\*SubscriptBox[\(u\), \(i\)]\) \[Element] {r,d,s} and m \[Element] \[CapitalNu]. The product is non-commutative. Finite products of creation operators form the algebra S(\!\(\*SuperscriptBox[OverscriptBox[\(h\), \(^\)], \(i\)]\)). Expects a list of \!\(\*SubscriptBox[\(u\), \(i\)]\)[m].";


(* ::Input::Initialization:: *)
tp::usage="tp[prod[{list_roots},exp[limCombo_roots]] is the tensor product of an element from the vector space of finite products of creation operators S(\!\(\*SuperscriptBox[OverscriptBox[\(h\), \(^\)], \(i\)]\)) and the twisted group algebra \!\(\*TemplateBox[{},\n\"Reals\"]\){\[CapitalLambda]}. tp is an element of the Fock space \[ScriptCapitalF]. The functions opA, opB, com and toTp return a tp.";


(* ::Input::Initialization:: *)
sortProd::usage="sortProd[linCombo_tp] expects a linear combination of tp[prod[{...}],exp[...]]. Returns that same linear combination with the elements of prod[{...}] normal ordered.";


(* ::Input::Initialization:: *)
com::usage="com[state_1, state_2] computes the commutator of two states from the Fock space \[ScriptCapitalF]. Takes linear combinations of ddfProd or tp as arguments. Returns a sum of tensor producs tp.";


(* ::Input::Initialization:: *)
eps::usage="eps[root_1,root_2] defines the cocylce factor of two roots. Is a bimultitplicative function. If root_1 or root_2 is a sum of roots, eps[root_1,root_2] simplifies to a product of coclyce factors of simple roots and the affine null root. The conventions are as follows: eps[r,r] = -1, eps[d,d] = 1, eps[s,s] = -1, eps[r,s] = eps[s,r] = 1, eps[d,s] = eps[s,d] = 1 and eps[d,r] = - eps[r,d] = 1.";


(* ::Input::Initialization:: *)
a::usage="a[l,n] computes the tachionyc momentum of level l and weight n according to the formula a[l,n] = -l * r - (l + (n^2 - 1)/l) d + n * s.";


(* ::Input::Initialization:: *)
virasoroOp::usage="virasoroOp[m][state] computes the action of the Virasoro operator with mode number m on a state. Expects the state to be an elment of the Fock space \[ScriptCapitalF], i.e. a linear combination of tensor products tp[prod[{...}],exp[...]]. A state is called physical if it satisfies (virasoroOp[m][state] - KroneckerDelta[m,0] * state) = 0 for all m \[GreaterEqual] 0.";


(* ::Input::Initialization:: *)
ddfTp::usage="ddfTp[linCombo_ddfProd_1,linCombo_ddfProd_2] defines the tensor product of two DDF states. Takes two arguments, which are linear combinations of ddfProd. The DDF tensor product ddfTp is used to compute the action of the coset Virasoro operator on tensor products of DDF states.";


(* ::Input::Initialization:: *)
ddfProd::usage="ddfProd[{list_AB},exp[linCombo_roots]] defines a DDF state. Takes two arguments. The first argument is a list of transversal and longitudinal DDF operators A[l,m] and B[l,m]. The second argument is a tachyonic ground state exp[linCombo_roots]. If the list of DDF operators is not normal ordered or contains annihilation operators ddfProd will order the product and act with the annihilation operators respecting the commutation relations of DDF operators. With the function toTp a ddfProd is converted into a sum of tensor products tp[prod[{...}],exp[...]].";


(* ::Input::Initialization:: *)
toTp::usage="toTp[linCombo_ddfProd] maps a ddfProd into a tensor product tp[prod[{...}],exp[...]]. If possible it will read the association from a .txt file stored in the folder ddf_states. If the required file does not exist it proceeds with a manual calculation. If it is expected that the manual calculation can take a long time a warining message is issued. Expects a linear combination of ddfProd. Returns a linear combination of tp.";


(* ::Input::Initialization:: *)
toDDF::usage="toDDF[linCombo_tp] turns a linear combination of tp[prod[{...}],exp[...]] into a linear combintation of ddfProd[{...},exp[...]]. Works only if a basis of ddfProds with the correct level, depth and weight for the tensor products exisits in the folder ddf_states. Otherwise the unevaluated expression is returned together with an error message.";


(* ::Input::Initialization:: *)
rank::usage="rank[list_ddfProd] and rank[list_tp] returns the rank of the list of ddfProd or tp. Returns an integer.";


(* ::Input::Initialization:: *)
linearIndependenQ::usage="linearIndependenQ[list_ddfProd], linearIndependenQ[list_ddfTp] and linearIndependenQ[list_tp] checks if the elements in a list of ddfProd, ddfTp or tp are linearly independent. Returns a boolean.";


(* ::Input::Initialization:: *)
fileNamesList::usage="fileNamesList[l, m, n] creates a list of all file names for the DDF states of a given level l, mode m and weight n. Returns a list of strings.";


(* ::Input::Initialization:: *)
ddfStatesList::usage="ddfStatesList[l, m, n] creates a list of all DDF states for a given level l, mode m and weight n. Returns a list of ddfProd.";


(* ::Input::Initialization:: *)
sugawaraOp::usage="sugwaraOp[m][linCombo_ddfProd] computes the action of the mode m Sugawara operator on a linear combination of ddfProd (or a tachyon exp[...]). The definition of the operator is derived in [2]. Returns a linear combination of ddfProd.";


(* ::Input::Initialization:: *)
affineE::usage="affineE[m][linCombo_ddfProd] or affineE[m][ddfTp[...]] computes the action of the mode m affine generator E on a linear combination of ddfProd (or a tachyon exp[...]) or a DDF tensor product ddfTp. The definition of the operator is derived in [2]. For the action on a ddfTp two levels are expected as arguments corresponding to the two arguments of the ddfTP. Returns a linear combination of ddfProd or ddfTp depending on the input" ;


(* ::Input::Initialization:: *)
affineF::usage="affineF[m][linCombo_ddfProd] or affineF[m][ddfTp[...]] computes the action of the mode m affine generator F on a linear combination of ddfProd (or a tachyon exp[...]) or a DDF tensor product ddfTp. The definition of the operator is derived in [2]. For the action on a ddfTp two levels are expected as arguments corresponding to the two arguments of the ddfTP. Returns a linear combination of ddfProd or ddfTp depending on the input" ;


(* ::Input::Initialization:: *)
affineH::usage="affineH[m][linCombo_ddfProd] or affineH[m][ddfTp[...]] computes the action of the mode m affine generator H on a linear combination of ddfProd (or a tachyon exp[...]) or a DDF tensor product ddfTp. The affine generator is defined as \!\(\*SubscriptBox[\(H\), \(m\)]\) = \!\(\*SqrtBox[\(2\)]\)\!\(\*SuperscriptBox[\(\[InvisiblePrefixScriptBase]\), \([l]\)]\)\!\(\*SubscriptBox[\(A\), \(lm\)]\). For the action on a ddfTp two levels are expected as arguments corresponding to the two arguments of the ddfTP. Returns a linear combination of ddfProd or ddfTp depending on the input" ;


(* ::Input::Initialization:: *)
e::usage="e[i] is the Chevalley-Serre generator e_i with i \[Element] {-1,0,1}.";


(* ::Input::Initialization:: *)
f::usage="f[i] is the Chevalley-Serre generator f_i with i \[Element] {-1,0,1}.";


(* ::Input::Initialization:: *)
h::usage="h[i] is the Chevalley-Serre generator h_i with i \[Element] {-1,0,1}.";


(* ::Input::Initialization:: *)
multiCom::usage="multiCom[indices] computes the multicommutator e_indices, where indices are from the set -1, 0, 1. Takes two or more arguments. Returns a tp.";


(* ::Input::Initialization:: *)
cosetVirasoroOpTp::usage="cosetVirasoroOpTp[m][ddfTp[expr_1,expr_2]] computes the action of the coset Virasoro operator on the tensor product ddfTp[expr_1, expr_2], where the two expressions are linear combinations of ddfProd. Returns a linear combination of ddfTp. The tensor product of DDF states does form a representation of the coset Virasoro algebra.";


(* ::Input::Initialization:: *)
sugawaraOpTp::usage="sugawaraOpTp[m][ddfTp[expr_1,expr_2]] computes the action of the Sugawara operator on the tensor product ddfTp[expr_1, expr_2], where the two expressions are linear combinations of ddfProd. Returns a linear combination of ddfTp.";


(* ::Section:: *)
(*Begin Private*)


(* ::Input::Initialization:: *)
Begin["`Private`"]


(* ::Section:: *)
(*Cartan Matrix*)


(* ::Text:: *)
(*Define the Cartan matrix.*)


(* ::Input::Initialization:: *)
cartanMatrix={{2,-1,0},{-1,2,-2},{0,-2,2}};


(* ::Section:: *)
(*Scalar Product*)


(* ::Text:: *)
(*Define the scalar product sp of roots according to the Cartan matrix.*)


(* ::Text:: *)
(*Make sp bi-linear.*)


(* ::Input::Initialization:: *)
sp[Plus[a_,b_],c_]:=sp[a,c]+sp[b,c]
sp[a_,Plus[b_,c_]]:=sp[a,b]+sp[a,c]


(* ::Input::Initialization:: *)
sp[n_?NumericQ a_,b_]:=n sp[a,b]
sp[a_,n_?NumericQ b_]:=n sp[a,b]


(* ::Input::Initialization:: *)
sp[_,0]:=0
sp[0,_]:=0


(* ::Text:: *)
(*Define the scalar product of simple roots according to the Cartan matrix.*)


(* ::Input::Initialization:: *)
sp[r,r]=2;
sp[d,d]=0;
sp[s,s]=2;
sp[r,d]=-1;
sp[d,r]=-1;
sp[s,d]=0;
sp[d,s]=0;
sp[r,s]=0;
sp[s,r]=0;


(* ::Section:: *)
(*Product*)


(* ::Text:: *)
(*Define the product prod of elements from the vector space of roots.*)


(* ::Text:: *)
(*The empty product is equal to 1.*)


(* ::Input::Initialization:: *)
prod[{}]:=1


(* ::Text:: *)
(*A product containing a zero is zero.*)


(* ::Input::Initialization:: *)
prod[{___,0,___}]:=0


(* ::Text:: *)
(*Make prod multi-linear; except on formal sums.*)


(* ::Input::Initialization:: *)
prod[{ls1___,Plus[a_,b_],ls2___}]:=prod[{ls1,a,ls2}]+prod[{ls1,b,ls2}]


(* ::Input::Initialization:: *)
prod[{ls1___,Times[n_?NumericQ,a_],ls2___}]:=n*prod[{ls1,a,ls2}]


(* ::Text:: *)
(*Define a second product for creation operators only that removes op1 and op2 wrappers and returns a normal ordered prod.*)


(* ::Text:: *)
(*Make prodCreation multi-linear; even on formal sums.*)


(* ::Input::Initialization:: *)
prodCreation[{ls1___,Plus[a_,b_],ls2___}]:=prodCreation[{ls1,a,ls2}]+prodCreation[{ls1,b,ls2}]


(* ::Input::Initialization:: *)
prodCreation[{ls1___,Times[n_?NumericQ,a_],ls2___}]:=n*prodCreation[{ls1,a,ls2}]


(* ::Input::Initialization:: *)
prodCreation[{ls1___,Times[z^n_.,a_],ls2___}]:=z^n*prodCreation[{ls1,a,ls2}]


(* ::Input::Initialization:: *)
prodCreation[{ls1___,Sum[g_*op1[h_],limits_],ls2___}]:=Sum[g*prodCreation[{ls1,op1[h],ls2}],limits]


(* ::Text:: *)
(*Remove op1 and op2 wrappers.*)


(* ::Input::Initialization:: *)
prodCreation[{ls1___,op1[u_],ls2___}]:=prodCreation[{ls1,u,ls2}]


(* ::Input::Initialization:: *)
prodCreation[{ls1___,op2[u_],ls2___}]:=prodCreation[{ls1,u,ls2}]


(* ::Text:: *)
(*Return normal ordered prod.*)


(* ::Input::Initialization:: *)
prodCreation[ls_]:=prod[Sort[ls]]/;FreeQ[ls,op1]&&FreeQ[ls,op2]


(* ::Section:: *)
(*Tensor Product*)


(* ::Text:: *)
(*Define the tensor product tp[prod[{list_roots},exp[limCombo_roots]] of an element from the vector space of finite products of creation operators S(\!\(\*SuperscriptBox[OverscriptBox[\(h\), \(^\)], \(i\)]\)) and the twisted group algebra \!\(\*TemplateBox[{},\n\"Reals\"]\){\[CapitalLambda]}. *)
(*tp is an element of the Fock space \[ScriptCapitalF]. *)
(*The functions opA, opB, com and toTp return a tp.*)


(* ::Text:: *)
(*Make tp linear in the first argument.*)


(* ::Input::Initialization:: *)
tp[0,_]:=0


(* ::Input::Initialization:: *)
tp[1,exp[t_]]:=exp[t]


(* ::Input::Initialization:: *)
tp[n_?NumericQ*a_,exp[t_]]:=n*tp[a,exp[t]]


(* ::Input::Initialization:: *)
tp[Plus[a_,b_],exp[t_]]:=tp[a,exp[t]]+tp[b,exp[t]]


(* ::Input::Initialization:: *)
tp[Times[a_,Plus[b_,c_]],exp[t_]]:=tp[a*b,exp[t]]+tp[a*c,exp[t]]


(* ::Input::Initialization:: *)
tp[z^m_.*a_,exp[t_]]:=z^m*tp[a,exp[t]]


(* ::Text:: *)
(*Pull out formal sums.*)


(* ::Input::Initialization:: *)
tp[a_.*Sum[b_,limits__],exp[t_]]:=Sum[tp[a*b,exp[t]],limits]


(* ::Text:: *)
(*Combine products in the first argument of the tensor product. *)


(* ::Input::Initialization:: *)
tp[a_.*prod[{ls1__}]*prod[{ls2__}],exp[t_]]:=tp[a*prod[Sort[{ls1,ls2}]],exp[t]]


(* ::Input::Initialization:: *)
tp[a_.*prod[{ls1__}]^n_,exp[t_]]:=tp[a*prod[Sort[Flatten[Table[{ls1},n]]]],exp[t]]


(* ::Section:: *)
(*Sort Tensor Products*)


(* ::Text:: *)
(*Define a function sortProd that sorts the product in the first argument of the tensor product.*)


(* ::Text:: *)
(*Make sortProd linear*)


(* ::Input::Initialization:: *)
sortProd[f_+g_]:=sortProd[f]+sortProd[g]


(* ::Input::Initialization:: *)
sortProd[n_?NumericQ*f_]:=n*sortProd[f]


(* ::Input::Initialization:: *)
sortProd[f_*tp[g__]]:=f*sortProd[tp[g]]


(* ::Input::Initialization:: *)
sortProd[eps[a_,b_]*c_]:=eps[a,b]*sortProd[c]


(* ::Input::Initialization:: *)
sortProd[f_]:=f


(* ::Text:: *)
(*Define sortProd.*)


(* ::Input::Initialization:: *)
sortProd[tp[prod[ls_],g_]]:=tp[prod[Sort[ls]],g]


(* ::Section:: *)
(*DDF Product*)


(* ::Text:: *)
(*DDF states are formed from DDF products denoted by ddfProd. *)
(*The function takes two arguments. The first argument is a list of transversal and longitudinal DDF operators A[l,m] and B[l,m]. The second argument is a tachyonic ground state exp[...]. *)
(*If the list of DDF operators is not normal ordered or contains annihilation operators ddfProd will automatically order the product and act with the annihilation operators respecting the commutation relations of DDF operators. *)
(*With the function toTp a ddfProd is converted into a tensor product tp[...].*)


(* ::Text:: *)
(*Make ddfProd linear.*)


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


(* ::Text:: *)
(*Define a second ddfProd, called ddfProdHold, which is not evaluated.*)
(*It only takes one argument; a list of DDF operators. *)
(*It is made to be joined to a ddfProd with the function joinProd.*)


(* ::Text:: *)
(*Give ddfProdHold the usual properties of a product.*)


(* ::Input::Initialization:: *)
ddfProdHold[{ls1___,Plus[a_,b_],ls2___}]:=ddfProdHold[{ls1,a,ls2}]+ddfProdHold[{ls1,b,ls2}]


(* ::Input::Initialization:: *)
ddfProdHold[{ls1___,Times[n_?NumericQ,a_],ls2___}]:=n*ddfProdHold[{ls1,a,ls2}]


(* ::Input::Initialization:: *)
ddfProdHold[{ls1___,0,ls2___}]:=0


(* ::Section:: *)
(*Join DDF Products*)


(* ::Text:: *)
(*joinProd takes a ddfProd and a ddfProdHold and joins them together.*)
(*This function is used to facilitate the evaluation of the Sugawara operator and the affine generators.*)


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
(*We introduce the tensor product of DDF states.*)
(*The tensor algebra is bigger than the Feingold-Frenkel algebra.*)
(*Only the tensor algebra gives rise to a representation of the coset Virasoro operator.*)
(*Replacing the tensor product with the commutator reduces the tensor algebra to the Feingold Frenkel algebra.*)


(* ::Text:: *)
(*In particular, the DDF tensor product is used to compute the action of the coset Virasoro operator on virtual states.*)


(* ::Text:: *)
(*We give some general properties*)


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


(* ::Text:: *)
(*Deal with tachyonic states*)


(* ::Input::Initialization:: *)
ddfTp[a_,ddfProd[{},exp[t_]]]:=ddfTp[a,exp[t]]
ddfTp[ddfProd[{},exp[t_]],a_]:=ddfTp[exp[t],a]


(* ::Section:: *)
(*Mode Number Adder*)


(* ::Text:: *)
(*We define a function modeNoAdder that adds all the mode numbers in a ddfProd or tp.*)


(* ::Text:: *)
(*Define auxiliary modeNo function that returns the mode number DDF operators and elements from the vector space of roots.*)


(* ::Input::Initialization:: *)
modeNo[A[level_,m_]]:=-m


(* ::Input::Initialization:: *)
modeNo[B[level_,m_]]:=-m


(* ::Input::Initialization:: *)
modeNo[r[m_]]:=-m


(* ::Input::Initialization:: *)
modeNo[d[m_]]:=-m


(* ::Input::Initialization:: *)
modeNo[s[m_]]:=-m


(* ::Text:: *)
(*Give recursive definition.*)


(* ::Input::Initialization:: *)
modeNoAdder[ddfProd[ls_,a_]]:=Sum[modeNo[elem],{elem,ls}]


(* ::Input::Initialization:: *)
modeNoAdder[tp[prod[ls_],a_]]:=Sum[modeNo[elem],{elem,ls}]


(* ::Section:: *)
(*Tensor Product Investigator*)


(* ::Text:: *)
(*Define a function tpInvestigator that grabs the level, mode sum and weight of a linear combination of tensor products tp and writes them in a list.*)


(* ::Text:: *)
(*tpInvestigator assumes that all tp in a sum have the same properties.*)
(*Hence it only picks one term from a linear combination of tp.*)


(* ::Input::Initialization:: *)
tpInvestigator[Plus[a_,b_]]:=tpInvestigator[a]


(* ::Input::Initialization:: *)
tpInvestigator[Times[a_, Plus[b_,c_]]]:=tpInvestigator[a*c]


(* ::Input::Initialization:: *)
tpInvestigator[n_*tp[a_,b_]]:=tpInvestigator[tp[a,b]]


(* ::Input::Initialization:: *)
tpInvestigator[0]={0,0,0};


(* ::Text::Bold:: *)
(*Extract information from a tp in the form {LEVEL, MODE, WEIGHT}*)


(* ::Input::Initialization:: *)
tpInvestigator[tp[ls_,exp[t_]]]:={sp[d,Expand[t]],modeNoAdder[tp[ls,exp[t]]],1/2sp[s,Expand[t]]}


(* ::Input::Initialization:: *)
tpInvestigator[n_*exp[t_]]:=tpInvestigator[exp[t]]


(* ::Input::Initialization:: *)
tpInvestigator[exp[t_]]:={sp[d,Expand[t]],0,1/2sp[s,Expand[t]]}


(* ::Section:: *)
(*DDF Product Investigator*)


(* ::Text:: *)
(*Define a function ddfProdInvestigator that grabs the level, mode sum and weight of a linear combination of DDF products ddfProd and writes them in a list.*)


(* ::Text:: *)
(*ddfProdInvestigator assumes that all ddfProd in a sum have the same properties.*)
(*Hence it only picks one term from a linear combination of ddfProd.*)


(* ::Input::Initialization:: *)
ddfProdInvestigator[Plus[a_,b_]]:=ddfProdInvestigator[a]


(* ::Input::Initialization:: *)
ddfProdInvestigator[Times[a_, Plus[b_,c_]]]:=ddfProdInvestigator[a*c]


(* ::Input::Initialization:: *)
ddfProdInvestigator[n_*ddfProd[a_,b_]]:=ddfProdInvestigator[ddfProd[a,b]]


(* ::Text::Bold:: *)
(*Extract information from a tp in the form {LEVEL, MODE, WEIGHT}*)


(* ::Input::Initialization:: *)
ddfProdInvestigator[ddfProd[ls_,exp[t_]]]:={sp[d,Expand[t]],modeNoAdder[ddfProd[ls,exp[t]]],1/2sp[s,Expand[t]]}


(* ::Input::Initialization:: *)
ddfProdInvestigator[n_*exp[t_]]:=ddfProdInvestigator[exp[Expand[t]]]


(* ::Input::Initialization:: *)
ddfProdInvestigator[exp[t_]]:={sp[d,Expand[t]],0,1/2sp[s,Expand[t]]}


(* ::Section:: *)
(*DDF Tensor Product Investigator*)


(* ::Text:: *)
(*Define a function ddfTpInvestigator that grabs the level, mode sum and weight for both factors in a linear combination of ddfTp and writes them in a list.*)


(* ::Text:: *)
(*ddfTpInvestigator assumes that all ddfTp in a sum have the same properties.*)
(*Hence it only picks one term from a linear combination of ddfProd.*)


(* ::Input::Initialization:: *)
ddfTpInvestigator[Plus[a_,b_]]:=ddfTpInvestigator[a]


(* ::Input::Initialization:: *)
ddfTpInvestigator[Times[a_, Plus[b_,c_]]]:=ddfTpInvestigator[a*c]


(* ::Input::Initialization:: *)
ddfTpInvestigator[n_*ddfTp[a_,b_]]:={ddfProdInvestigator[a],ddfProdInvestigator[b]}


(* ::Input::Initialization:: *)
ddfTpInvestigator[ddfTp[a_,b_]]:={ddfProdInvestigator[a],ddfProdInvestigator[b]}


(* ::Section:: *)
(*Linear Independence Check and Rank*)


(* ::Text:: *)
(*Define a function linerIndependenQ that checks if the list of ddfProd , ddfTp or tp is linearly independent.*)


(* ::Input::Initialization:: *)
rank[ls_]:=Block[{},coefficientList=DeleteCases[DeleteDuplicates[Flatten[Table[ReplaceAll[If[Head[elem]===Plus,Apply[List,elem],elem],{n_*ddfProd[expr__]->ddfProd[expr],n_*ddfTp[expr__]->ddfTp[expr],n_*tp[expr__]->tp[expr],n_*exp[expr_]->exp[expr]}],{elem,ls}]]],0];MatrixRank[Table[Table[Coefficient[elem,coefficient],{coefficient,coefficientList}],{elem,ls}]]]


(* ::Input::Initialization:: *)
linearIndependenQ[ls_]:=Block[{},If[rank[ls]==Length[ls],True,False]]


(* ::Section:: *)
(*Vertex Operator*)


(* ::Text:: *)
(*Define the vertex operator vertexOp of an element from the the vector space of roots  Subscript[\[CapitalLambda], \[DoubleStruckCapitalR]]. *)
(*Elements from the vector space of roots are wrapped with op1 functions for the action of the Vertex operator and the  commutation relations defined below.*)


(* ::Input::Initialization:: *)
vertexOp[u_[n_]]:=Module[{l},\!\(
\*UnderoverscriptBox[\(\[Sum]\), \(l = 0\), \(\[Infinity]\)]\(\((\((
\*SuperscriptBox[\((\(-1\))\), \(n - 1\)]\ \(\((l - n - 1)\)!\))\)\ op1[u[l]]\ 
\*SuperscriptBox[\(z\), \(\(-l\) + n\)])\)/\((\(l!\)\ \(\((\(-n\) - 1)\)!\))\)\)\)+\!\(
\*UnderoverscriptBox[\(\[Sum]\), \(l = 0\), \(\[Infinity]\)]\(\((\(\((l - n - 1)\)!\)\ op1[u[\(-l\) + n]]\ 
\*SuperscriptBox[\(z\), \(l\)])\)/\((\(l!\)\ \(\((\(-n\) - 1)\)!\))\)\)\)]


(* ::Text:: *)
(*The  definition  is  derived  from  (2.92)  and  (2.100)  in [1] .*)


(* ::Section:: *)
(*The Operator Functions*)


(* ::Text:: *)
(*Make op1 and op2 linear and set op1[0] = 0.*)


(* ::Input::Initialization:: *)
op1[0]:=0


(* ::Input::Initialization:: *)
op1[Plus[a_,b_]]:=op1[a]+op1[b]


(* ::Input::Initialization:: *)
op2[Plus[a_,b_]]:=op2[a]+op2[b]


(* ::Input::Initialization:: *)
op1[n_?NumericQ*a_]:=n*op1[a]


(* ::Input::Initialization:: *)
op2[n_?NumericQ*a_]:=n*op2[a]


(* ::Section:: *)
(*Basic Operator Commutation Relations*)


(* ::Text:: *)
(*Define  the commutation relations basicCom between op1 and op2 operators.*)
(*op1 are the normal ordered operators. They commute among each other, but not with the other operators op2.*)


(* ::Text:: *)
(*Make basicCom linear*)


(* ::Input::Initialization:: *)
basicCom[0,a_]:=0


(* ::Input::Initialization:: *)
basicCom[a_,0]:=0


(* ::Input::Initialization:: *)
basicCom[n_?NumericQ*a_,b_]:=n*basicCom[a,b]


(* ::Input::Initialization:: *)
basicCom[a_,n_?NumericQ*b_]:=n*basicCom[a,b]


(* ::Input::Initialization:: *)
basicCom[Plus[a_,b_],c_]:=basicCom[a,c]+basicCom[b,c]


(* ::Input::Initialization:: *)
basicCom[a_,Plus[b_,c_]]:=basicCom[a,b]+basicCom[a,c]


(* ::Input::Initialization:: *)
basicCom[Sum[a_*Plus[b_,c_],limits_],d_]:=Sum[a*(basicCom[b,d]+basicCom[c,d]),limits]


(* ::Text:: *)
(*Give specific definitions.*)


(* ::Input::Initialization:: *)
basicCom[op1[s_[n_]],op1[u_[m_]]]:=0


(* ::Input::Initialization:: *)
basicCom[op1[s_[n_]],op2[u_[m_]]]:=n*KroneckerDelta[n+m,0]*sp[s,u]


(* ::Input::Initialization:: *)
basicCom[Sum[a_*op1[s_[n_]],limits_],op1[u_[m_]]]:=0


(* ::Input::Initialization:: *)
basicCom[op1[u_[m_]],Sum[a_*op1[s_[n_]],limits_]]:=0


(* ::Input::Initialization:: *)
basicCom[Sum[a_*op1[s_[n_]],limits_],op2[u_[m_]]]:=Sum[a*n*KroneckerDelta[n+m,0]*sp[s,u],limits]


(* ::Input::Initialization:: *)
basicCom[Sum[a_*op1[s_[n_]],limits1_],Sum[b_*op1[u_[m_]],limits2_]]:=0


(* ::Text:: *)
(*The relations here follow from (2.73) in [1].*)


(* ::Section:: *)
(*Test if an Operator is an Annihilation Operator*)


(* ::Text:: *)
(*Test if an operator op1[u[n]] is an annihilation operator with the function isAnnihilator. *)
(*This is the case if n >= 0. *)
(*Returns a boolean.*)


(* ::Input::Initialization:: *)
isAnnihilator[op1[u_[n_]]]:=If[n>=0,True,False]


(* ::Input::Initialization:: *)
isAnnihilator[op2[u_[n_]]]:=If[n>=0,True,False]


(* ::Text:: *)
(*Return true if at least one operator in a sum of operators is an annihilation operator.*)


(* ::Input::Initialization:: *)
isAnnihilator[\!\(\*
TagBox[
StyleBox[
RowBox[{"Sum", "[", 
RowBox[{
RowBox[{"f_", "*", 
RowBox[{"op1", "[", 
RowBox[{"u_", "[", "n_", "]"}], "]"}]}], ",", "limits_"}], "]"}],
ShowSpecialCharacters->False,
ShowStringCharacters->True,
NumberMarks->True],
FullForm]\)]:=MemberQ[Sum[f*isAnnihilator[op1[u[n]]],limits],True]


(* ::Input::Initialization:: *)
isAnnihilator[\!\(\*
TagBox[
StyleBox[
RowBox[{"a_", "*", 
RowBox[{"Sum", "[", 
RowBox[{
RowBox[{"f_", "*", 
RowBox[{"op1", "[", 
RowBox[{"u_", "[", "n_", "]"}], "]"}]}], ",", "limits_"}], "]"}]}],
ShowSpecialCharacters->False,
ShowStringCharacters->True,
NumberMarks->True],
FullForm]\)]:=MemberQ[Sum[f*isAnnihilator[op1[u[n]]],limits],True]


(* ::Text:: *)
(*Define a few special cases for exponentials, powers and logarithms such as in (2.95) of [1].*)


(* ::Input::Initialization:: *)
isAnnihilator[exp[f_]]:=True


(* ::Input::Initialization:: *)
isAnnihilator[log[1+a_.*Sum[op1[d[-i]]z^i,{i,1,Infinity}]+a_.*Sum[op1[d[i]]z^-i,{i,1,Infinity}]]]:=True


(* ::Input::Initialization:: *)
isAnnihilator[log[1+a_.*Sum[op1[d[-i]]z^i,{i,1,Infinity}]]]:=False


(* ::Input::Initialization:: *)
isAnnihilator[pow[1+a_.*Sum[op1[d[-i]]z^i,{i,1,Infinity}]+a_.*Sum[op1[d[i]]z^-i,{i,1,Infinity}],n_]]:=True


(* ::Input::Initialization:: *)
isAnnihilator[pow[1+a_.*Sum[op1[d[-i]]z^i,{i,1,Infinity}],n_]]:=False


(* ::Text:: *)
(*Check  if  a  list contains an annihilation operator.*)


(* ::Input::Initialization:: *)
containsAnnihilator[ls_]:=MemberQ[Map[isAnnihilator,ls],True]


(* ::Section:: *)
(*Operator Action*)


(* ::Text:: *)
(*Define the action of op1 on a tensor product.*)
(*Thus define the functions act, action and sort.*)


(* ::Text:: *)
(*Define  the trivial action.*)


(* ::Input::Initialization:: *)
action[prod[{}],exp[t_]]:=1


(* ::Input::Initialization:: *)
action[0,exp[t_]]:=0


(* ::Text:: *)
(*Make action linear and pull out anything that does not belong to prod.*)


(* ::Input::Initialization:: *)
action[Plus[a_,b_],exp[t_]]:=action[a,exp[t]]+action[b,exp[t]]


(* ::Input::Initialization:: *)
action[f_*prod[ls_],exp[t_]]:=f*action[prod[ls],exp[t]]


(* ::Text:: *)
(*Give  the main definition recursively.*)
(*Check if the last operator in the operator product is an annihilation operator. If so apply it to the second component of the tensor product and then apply the function action again.*)
(*If the last term is not an annihilation operator check if any of the other operators is. If this is true commute one annihilation operator and one creation operator such that the annihilation operator moves to the right. Afterwards apply the function action again.*)
(*If there is no annihilation operator in the list rename prod to prodCreation and do not apply action again*)


(* ::Input::Initialization:: *)
action[prod[{ls___,a_}],exp[t_]]:=If[isAnnihilator[a],action[act[prod[{ls,a}],exp[t]],exp[t]],If[containsAnnihilator[{ls}],action[sort[prod[{ls,a}]],exp[t]],prodCreation[{ls,a}]]]


(* ::Text:: *)
(*Exchange  one creation and one annihilation operator in the product.*)


(* ::Input::Initialization:: *)
sort[prod[{ls1___,a_,b_,ls2___}]]:=basicCom[a,b]prod[{ls1,ls2}]+prod[{ls1,b,a,ls2}]/;FreeQ[a,exp]&&FreeQ[a,log]&&FreeQ[a,pow]&&isAnnihilator[a]&&!isAnnihilator[b]


(* ::Text:: *)
(*Consider  the special case of the exponential function.*)


(* ::Input::Initialization:: *)
sort[prod[{ls1___,exp[a_],b_,ls2___}]]:=basicCom[a,b]prod[{ls1,exp[a],ls2}]+prod[{ls1,b,exp[a],ls2}]/;!isAnnihilator[b]


(* ::Text:: *)
(*Consider  the special case of the logarithm.*)


(* ::Input::Initialization:: *)
sort[prod[{ls1___,log[1+a_],b_,ls2___}]]:=basicCom[a,b]prod[{ls1,pow[1+a,-1],ls2}]+prod[{ls1,b,log[1+a],ls2}]/;!isAnnihilator[b]


(* ::Text:: *)
(*Consider  the special case of powers of a series.*)


(* ::Input::Initialization:: *)
sort[prod[{ls1___,pow[1+a_,n_],b_,ls2___}]]:=n*basicCom[a,b]prod[{ls1,pow[1+a,n-1],ls2}]+prod[{ls1,b,pow[1+a,n],ls2}]/;!isAnnihilator[b]


(* ::Text:: *)
(*Act  with the last element in the operator product on the second component of the tensor product.*)


(* ::Input::Initialization:: *)
act[prod[{ls___,op1[u_[n_]]}],exp[t_]]:=If[n>0,0,If[n==0,sp[u,t]*prod[{ls}],prod[{ls,op1[u[n]]}]]]


(* ::Input::Initialization:: *)
act[prod[{ls___,exp[_]}],exp[t_]]:=prod[{ls}]


(* ::Input::Initialization:: *)
act[prod[{ls___,log[1+a_.*Sum[op1[d[-i]]z^i,{i,1,Infinity}]+a_.*Sum[op1[d[i]]z^-i,{i,1,Infinity}]]}],exp[t_]]:=prod[{ls,log[1+a*Sum[op1[d[-i]]z^i,{i,1,Infinity}]]}]


(* ::Input::Initialization:: *)
act[prod[{ls___,pow[1+a_.*Sum[op1[d[-i]]z^i,{i,1,Infinity}]+a_.*Sum[op1[d[i]]z^-i,{i,1,Infinity}],n_]}],exp[t_]]:=prod[{ls,pow[1+a*Sum[op1[d[-i]]z^i,{i,1,Infinity}],n]}]


(* ::Input::Initialization:: *)
act[prod[{ls___,Sum[a_*op1[s_[n_]],limits_]}],exp[t_]]:=Sum[a*KroneckerDelta[n,0],limits]*sp[s,t]*prod[{ls}]


(* ::Text:: *)
(*The  definitions are derived  from (2.117) - (2.120)  in [1] .*)


(* ::Section:: *)
(*Simplify Sums*)


(* ::Text:: *)
(*Define  a function sumSimp that combines multiple sums.*)


(* ::Text:: *)
(*If there is only one sum do nothing.*)


(* ::Input::Initialization:: *)
sumSimp[Sum[f_,limits__]]:=Sum[f,limits]/;FreeQ[f,Sum]


(* ::Text:: *)
(*Make  the sumSimp linear.*)


(* ::Input::Initialization:: *)
sumSimp[Plus[f_,g_]]:=sumSimp[f]+sumSimp[g]


(* ::Input::Initialization:: *)
sumSimp[Sum[Plus[f_,g_],limits__]]:=sumSimp[Sum[f,limits]]+sumSimp[Sum[g,limits]]


(* ::Input::Initialization:: *)
sumSimp[Sum[Times[f_,Plus[g_,h_]],limits__]]:=sumSimp[Sum[f*g,limits]]+sumSimp[Sum[f*h,limits]]


(* ::Text:: *)
(*Recursive definition of sumSimp*)


(* ::Input::Initialization:: *)
sumSimp[Sum[f_. * Sum[g_, limits1_], limits2__]] := If[FreeQ[f, Sum] && FreeQ[g, Sum], Sum[f * g, limits1, limits2], sumSimp[Sum[f * g, limits1,limits2]]]


(* ::Text:: *)
(*Define  a  functionfindSummationLimit that finds the upper limit for the sums involving fractions and logarithms*)


(* ::Input::Initialization:: *)
findSummationLimit[n_?NumericQ+b_]:=n+1


(* ::Input::Initialization:: *)
findSummationLimit[b_]:=0/;!NumericQ[b]


(* ::Text:: *)
(*Define  sumSimp on terms containing logarithms*)


(* ::Input::Initialization:: *)
sumSimp[Sum[f_.*z^m_ tp[g_.*prodCreation[{ls___,log[1+h_.*Sum[__]]}],exp[t_]],limits2__]]:=Sum[ExpandAll[f*z^m Sum[(-1)^(i1+1)/i1*tp[g*prodCreation[Flatten[{ls,Table[Sum[h*z^i2 d[-i2],{i2,1,-findSummationLimit[m]-i1+1}],i1]}]],exp[t]],{i1,1,-findSummationLimit[m]}]],limits2]/;FreeQ[f,Sum]


(* ::Text:: *)
(*Define  sumSimp on terms containing fractions*)


(* ::Input::Initialization:: *)
sumSimp[Sum[f_.*z^m_ tp[g_.*prodCreation[{ls___,pow[1+h_.*Sum[__],n_]}],exp[t_]],limits2__]]:=Sum[f*z^m tp[g*prodCreation[{ls}],exp[t]],limits2]+Sum[ExpandAll[f*z^m Sum[Binomial[n,i1]*tp[g*prodCreation[Flatten[{ls,Table[Sum[h*z^i2 d[-i2],{i2,1,-findSummationLimit[m]-i1+1}],i1]}]],exp[t]],{i1,1,-findSummationLimit[m]}]],limits2]/;FreeQ[f,Sum]


(* ::Section:: *)
(*Residue*)


(* ::Text:: *)
(*Define the residue function res.*)


(* ::Text:: *)
(*Make res linear and pull out formal sums.*)


(* ::Input::Initialization:: *)
res[Plus[f_,g_]]:=res[f]+res[g]


(* ::Input::Initialization:: *)
res[Times[f_,Plus[g_,h_]]]:=res[f*g]+res[f*h]


(* ::Input::Initialization:: *)
res[n_?NumericQ*Sum[f_,limits__]]:=n*Sum[res[f],limits]


(* ::Input::Initialization:: *)
res[Sum[f_,limits__]]:=Sum[res[f],limits]/;FreeQ[f,Sum]


(* ::Text:: *)
(*Give the main definition.*)


(* ::Input::Initialization:: *)
res[f_*z^m_*tp[a_,b_]]:=KroneckerDelta[m,-1]*f*tp[a,b]


(* ::Input::Initialization:: *)
res[z^m_*tp[a_,b_]]:=KroneckerDelta[m,-1]*tp[a,b]


(* ::Input::Initialization:: *)
res[f_*tp[a_,b_]]:=0


(* ::Input::Initialization:: *)
res[z*tp[a_,b_]]:=0


(* ::Input::Initialization:: *)
res[f_]:=0/;FreeQ[f,z]


(* ::Section:: *)
(*Schur Polynomials*)


(* ::Text:: *)
(*Define  a  function toList that write a linear combination of operators (usually roots) into a list*)


(* ::Input::Initialization:: *)
toList[f_]:=If[Head[f]===Symbol,{f},If[Head[f]===Times,{f/.Times->List},f/.Plus->List/.Times->List]]


(* ::Text:: *)
(*Define a function applyList that applies a linear combination of operators written as a list {{coeff1, op1}, {coeff2, op2, ...} to some value x. Returns coeff1 op1[x] + coeff2 op2[x] + .... .*)


(* ::Input::Initialization:: *)
applyList[ls_,x_]:=Sum[If[Length[i]==0,Apply[i,{x}],If[Length[i]==2,i[[1]]*Apply[i[[2]],{x}],Message[applyList::nnarg,i];Abort[]]],{i,ls}]


(* ::Input::Initialization:: *)
applyList::nnarg="The argument `1` is not a list of length 2. Aborting evaluation.";


(* ::Text:: *)
(*Define the Schur polynomials schurEval for roots from Subscript[\[CapitalLambda], \[DoubleStruckCapitalR]].*)


(* ::Text:: *)
(*The first eight Schur polynomials are defined explicitly.*)


(* ::Input::Initialization:: *)
rootSchurEval[m_,r_]:=0/;m<0


(* ::Input::Initialization:: *)
rootSchurEval[0,r_]:=1


(* ::Input::Initialization:: *)
rootSchurEval[1,r_]:=prod[{applyList[toList[r],-1]}]


(* ::Input::Initialization:: *)
rootSchurEval[2,r_]:=1/2 prod[{applyList[toList[r],-1],applyList[toList[r],-1]}]+1/2 prod[{applyList[toList[r],-2]}]


(* ::Text:: *)
(*The longer definitions are read from files.*)


(* ::Input::Initialization:: *)
Get[FileNameJoin[{"schur_polynomials","root_schur_3.wls"}]]


(* ::Input::Initialization:: *)
Get[FileNameJoin[{"schur_polynomials","root_schur_4.wls"}]]


(* ::Input::Initialization:: *)
Get[FileNameJoin[{"schur_polynomials","root_schur_5.wls"}]]


(* ::Input::Initialization:: *)
Get[FileNameJoin[{"schur_polynomials","root_schur_6.wls"}]]


(* ::Input::Initialization:: *)
Get[FileNameJoin[{"schur_polynomials","root_schur_7.wls"}]]


(* ::Text:: *)
(*For n > 7 the Schur polynomials are calculated at runtime.*)


(* ::Text:: *)
(*Define auxiliary product function auxProd to turn products into lists*)


(* ::Input::Initialization:: *)
auxProd[Plus[a_,b_],ls_]:=auxProd[a,ls]+auxProd[b,ls]


(* ::Input::Initialization:: *)
auxProd[n_?NumericQ*a_,ls_]:=n*auxProd[a,ls]


(* ::Input::Initialization:: *)
auxProd[applyList[a__],ls_]:=auxProd[1,Append[ls,applyList[a]]]


(* ::Input::Initialization:: *)
auxProd[applyList[a__]*b_,ls_]:=auxProd[b,Append[ls,applyList[a]]]


(* ::Input::Initialization:: *)
auxProd[Power[applyList[a__],n_],ls_]:=auxProd[1,Flatten[Append[ls,Table[applyList[a],n]]]]


(* ::Input::Initialization:: *)
auxProd[Power[applyList[a__],n_]*b_,ls_]:=auxProd[b,Flatten[Append[ls,Table[applyList[a],n]]]]


(* ::Text:: *)
(*In the end auxProd is replaced by prod.*)


(* ::Input::Initialization:: *)
auxProd[1,ls_]:=prod[Sort[ls]]


(* ::Text:: *)
(*Give definition of rootSchurEval for n > 7.*)


(* ::Input::Initialization:: *)
rootSchurEval[n_,r_]:=ReleaseHold[With[{root=r},Message[rootSchurEval::nnarg];
auxProd[ExpandAll[SeriesCoefficient[Series[Exp[Sum[1/j*applyList[toList[Hold[root]],-j]*z^j,{j,1,n}]],{z,0,n}],n]],{}]]]/;n>7


(* ::Input::Initialization:: *)
rootSchurEval::nnarg= "The Schur polynomial necessary for this calculation has not been pre-computed. Switching to manual evaluation. This might increase the calculation time.";


(* ::Section:: *)
(*Commutator*)


(* ::Text:: *)
(*Define  the commutator com between two states.*)
(*Expects tensor products tp or DDF products ddfProd as input.*)
(*Also the action of a DDF operator on a state is expressed as a commutator called ddfCom.*)
(*Only the commutator of two states gets a cocycle factor; not the DDF commutator.*)


(* ::Text:: *)
(*com and ddfCom and take their first argument, turn it into a Vertex operator and act with it on the second argument.*)
(*com and ddfCom  use action, vertexOp, sumSimp, res and the Schur polynomials rootSchurEval.*)


(* ::Text:: *)
(*Make com and ddfCom bi-linear.*)


(* ::Input::Initialization:: *)
com[_,0]:=0
com[0,_]:=0


(* ::Input::Initialization:: *)
ddfCom[_,0]:=0
ddfCom[0,_]:=0


(* ::Input::Initialization:: *)
com[Plus[a_,b_],c_]:=com[a,c]+com[b,c]
com[a_,Plus[b_,c_]]:=com[a,b]+com[a,c]


(* ::Input::Initialization:: *)
ddfCom[Plus[a_,b_],c_]:=ddfCom[a,c]+ddfCom[b,c]
ddfCom[a_,Plus[b_,c_]]:=ddfCom[a,b]+ddfCom[a,c]


(* ::Input::Initialization:: *)
com[Times[a_,Plus[b_,c_]],d_]:=com[a*b,d]+com[a*c,d]
com[a_,Times[b_,Plus[c_,d_]]]:=com[a,b*c]+com[a,b*d]


(* ::Input::Initialization:: *)
ddfCom[Times[a_,Plus[b_,c_]],d_]:=ddfCom[a*b,d]+ddfCom[a*c,d]
ddfCom[a_,Times[b_,Plus[c_,d_]]]:=ddfCom[a,b*c]+ddfCom[a,b*d]


(* ::Input::Initialization:: *)
com[a_*tp[b__],c_]:=a*com[tp[b],c]
com[a_,b_*tp[c__]]:=b*com[a,tp[c]]


(* ::Input::Initialization:: *)
com[a_*ddfProd[b__],c_]:=a*com[ddfProd[b],c]
com[a_,b_*ddfProd[c__]]:=b*com[a,ddfProd[c]]


(* ::Input::Initialization:: *)
ddfCom[a_*tp[b__],c_]:=a*ddfCom[tp[b],c]
ddfCom[a_,b_*tp[c__]]:=b*ddfCom[a,tp[c]]


(* ::Input::Initialization:: *)
com[a_*exp[b_],c_]:=a*com[exp[b],c]
com[a_,b_*exp[c_]]:=b*com[a,exp[c]]


(* ::Input::Initialization:: *)
ddfCom[a_*exp[b_],c_]:=a*ddfCom[exp[b],c]
ddfCom[a_,b_*exp[c_]]:=b*ddfCom[a,exp[c]]


(* ::Text:: *)
(*Replace ddfProd with tp.*)


(* ::Input::Initialization:: *)
com[ddfProd[a__],b_]:=com[toTp[ddfProd[a]],b]
com[a_,ddfProd[b__]]:=com[a,toTp[ddfProd[b]]]


(* ::Text:: *)
(*com and ddfCom of two general tensor product states.*)


(* ::Input::Initialization:: *)
com[tp[prod[ls1_],exp[r_]],tp[prod[ls2_],exp[t_]]]:=ReplaceAll[res[sumSimp[Sum[eps[r,t]tp[rootSchur[m,r]Power[z,m+sp[r,t]]action[prod[Flatten[{exp[\!\(
\*UnderoverscriptBox[\(\[Sum]\), \(n = 1\), \(\[Infinity]\)]\(\(-
\*FractionBox[\(1\), \(n\)]\) op1[applyList[toList[r], n]] 
\*SuperscriptBox[\(z\), \(-n\)]\)\)],Map[vertexOp,ls1],Map[op2,ls2]}]],exp[t]],exp[r+t]],{m,0,Infinity}]]],rootSchur->rootSchurEval]


(* ::Input::Initialization:: *)
ddfCom[tp[prod[ls1_],exp[r_]],tp[prod[ls2_],exp[t_]]]:=ReplaceAll[res[sumSimp[Sum[tp[rootSchur[m,r]Power[z,m+sp[r,t]]action[prod[Flatten[{exp[\!\(
\*UnderoverscriptBox[\(\[Sum]\), \(n = 1\), \(\[Infinity]\)]\(\(-
\*FractionBox[\(1\), \(n\)]\) op1[applyList[toList[r], n]] 
\*SuperscriptBox[\(z\), \(-n\)]\)\)],Map[vertexOp,ls1],Map[op2,ls2]}]],exp[t]],exp[r+t]],{m,0,Infinity}]]],rootSchur->rootSchurEval]//ExpandAll//sortProd


(* ::Text:: *)
(*com and ddfCom  of a general state with a tachyonic state.*)


(* ::Input::Initialization:: *)
com[tp[prod[ls1_],exp[r_]],exp[t_]]:=ReplaceAll[res[sumSimp[Sum[eps[r,t]tp[rootSchur[m,r]Power[z,m+sp[r,t]]action[prod[Flatten[{exp[\!\(
\*UnderoverscriptBox[\(\[Sum]\), \(n = 1\), \(\[Infinity]\)]\(\(-
\*FractionBox[\(1\), \(n\)]\) op1[applyList[toList[r], n]] 
\*SuperscriptBox[\(z\), \(-n\)]\)\)],Map[vertexOp,ls1]}]],exp[t]],exp[r+t]],{m,0,Infinity}]]],rootSchur->rootSchurEval]


(* ::Input::Initialization:: *)
ddfCom[tp[prod[ls1_],exp[r_]],exp[t_]]:=ReplaceAll[res[sumSimp[Sum[tp[rootSchur[m,r]Power[z,m+sp[r,t]]action[prod[Flatten[{exp[\!\(
\*UnderoverscriptBox[\(\[Sum]\), \(n = 1\), \(\[Infinity]\)]\(\(-
\*FractionBox[\(1\), \(n\)]\) op1[applyList[toList[r], n]] 
\*SuperscriptBox[\(z\), \(-n\)]\)\)],Map[vertexOp,ls1]}]],exp[t]],exp[r+t]],{m,0,Infinity}]]],rootSchur->rootSchurEval]//ExpandAll//sortProd


(* ::Text:: *)
(*When exchanging the arguments we do not simply get minus the commutator. Hence we must compute it explicitly.*)


(* ::Input::Initialization:: *)
com[exp[r_],tp[prod[ls2_],exp[t_]]]:=ReplaceAll[res[sumSimp[Sum[eps[r,t]tp[rootSchur[m,r]Power[z,m+sp[r,t]]action[prod[Flatten[{exp[\!\(
\*UnderoverscriptBox[\(\[Sum]\), \(n = 1\), \(\[Infinity]\)]\(\(-
\*FractionBox[\(1\), \(n\)]\) op1[applyList[toList[r], n]] 
\*SuperscriptBox[\(z\), \(-n\)]\)\)],Map[op2,ls2]}]],exp[t]],exp[r+t]],{m,0,Infinity}]]],rootSchur->rootSchurEval]


(* ::Input::Initialization:: *)
ddfCom[exp[r_],tp[prod[ls2_],exp[t_]]]:=ReplaceAll[res[sumSimp[Sum[tp[rootSchur[m,r]Power[z,m+sp[r,t]]action[prod[Flatten[{exp[\!\(
\*UnderoverscriptBox[\(\[Sum]\), \(n = 1\), \(\[Infinity]\)]\(\(-
\*FractionBox[\(1\), \(n\)]\) op1[applyList[toList[r], n]] 
\*SuperscriptBox[\(z\), \(-n\)]\)\)],Map[op2,ls2]}]],exp[t]],exp[r+t]],{m,0,Infinity}]]],rootSchur->rootSchurEval]//ExpandAll//sortProd


(* ::Text:: *)
(*com and ddfCom  of two tachyonic states.*)


(* ::Input::Initialization:: *)
com[exp[r_],exp[t_]]:=If[IntegerQ[sp[r,t]],eps[r,t]tp[ExpandAll[rootSchurEval[-1-sp[r,t],r]],exp[r+t]],0]


(* ::Input::Initialization:: *)
ddfCom[exp[r_],exp[t_]]:=tp[ExpandAll[rootSchurEval[-1-sp[r,t],r]],exp[r+t]]//ExpandAll//sortProd


(* ::Text:: *)
(*These equations generalize (2.120) from [1].*)


(* ::Text:: *)
(*For longitudinal DDF operators we need the commutator of the longitudinal Virasoro operator.*)


(* ::Text:: *)
(*For the general case we have*)


(* ::Input::Initialization:: *)
ddfCom[longitudinalVirasoroOp[l_,m_],tp[prod[ls2_],exp[t_]]]:=-ddfCom[tp[prod[{applyList[toList[t],-1]}],exp[m/l*d]],tp[prod[ls2],exp[t]]]-m/2*ReplaceAll[res[sumSimp[Sum[tp[rootSchur[n,m/l*d]*Power[z,n+m]action[prod[Flatten[{log[1+1/l \!\(
\*UnderoverscriptBox[\(\[Sum]\), \(i = 1\), \(\[Infinity]\)]\(op1[d[\(-i\)]] 
\*SuperscriptBox[\(z\), \(i\)]\)\)+1/l \!\(
\*UnderoverscriptBox[\(\[Sum]\), \(i = 1\), \(\[Infinity]\)]\(op1[d[i]] 
\*SuperscriptBox[\(z\), \(-i\)]\)\)],(m/l \!\(
\*UnderoverscriptBox[\(\[Sum]\), \(j = 1\), \(\[Infinity]\)]\(op1[d[\(-j\)]] 
\*SuperscriptBox[\(z\), \(j - 1\)]\)\)+m/l \!\(
\*UnderoverscriptBox[\(\[Sum]\), \(j = 0\), \(\[Infinity]\)]\(op1[d[j]] 
\*SuperscriptBox[\(z\), \(\(-j\) - 1\)]\)\)),exp[\!\(
\*UnderoverscriptBox[\(\[Sum]\), \(k = 1\), \(\[Infinity]\)]\(\(-
\*FractionBox[\(m\), \(l*k\)]\) op1[d[k]] 
\*SuperscriptBox[\(z\), \(-k\)]\)\)],Map[op2,ls2]}]],exp[t]],exp[m/l*d+t]],{n,0,Infinity}]]],rootSchur->rootSchurEval]-m/2 ReplaceAll[res[sumSimp[Sum[tp[rootSchur[n,m/l*d]*Power[z,n+m-1]action[prod[Flatten[{exp[\!\(
\*UnderoverscriptBox[\(\[Sum]\), \(k = 1\), \(\[Infinity]\)]\(\(-
\*FractionBox[\(m\), \(l*k\)]\) op1[d[k]] 
\*SuperscriptBox[\(z\), \(-k\)]\)\)],Map[op2,ls2]}]],exp[t]],exp[m/l*d+t]],{n,0,Infinity}]]],rootSchur->rootSchurEval]//ExpandAll//sortProd


(* ::Text:: *)
(*For the action on a tachyonic state we have*)


(* ::Input::Initialization:: *)
ddfCom[longitudinalVirasoroOp[l_,m_],exp[t_]]:=-ddfCom[tp[prod[{applyList[toList[t],-1]}],exp[m/l*d]],exp[t]]-m/2*ReplaceAll[res[ExpandAll[Sum[(-1)^(i-1)/i*tp[prodCreation[Table[Sum[1/l d[-j]z^j,{j,1,-m-i+1}],i]]*(m*z^-1+m/l Sum[prod[{d[-k]}]z^(k-1),{k,1,-m}])*Sum[rootSchur[n,m/l*d]*z^(n+m),{n,0,-m}],exp[m/l*d+t]],{i,1,-m}]]],rootSchur->rootSchurEval]-m/2*tp[rootSchurEval[-m,m/l*d],exp[m/l*d+t]]//ExpandAll//sortProd


(* ::Section:: *)
(*Cocycle Factor*)


(* ::Text:: *)
(*Define  the cocycle factor eps.*)


(* ::Text:: *)
(*Make eps bi-multiplicative.*)


(* ::Input::Initialization:: *)
eps[Plus[r_,s_],t_]:=eps[r,t]*eps[s,t]
eps[r_,Plus[s_,t_]]:=eps[r,s]*eps[r,t]


(* ::Input::Initialization:: *)
eps[r_,n_?IntegerQ*s_]:=eps[r,Sign[n]*s]^Abs[n]/;Abs[n]!=1


(* ::Input::Initialization:: *)
eps[n_?IntegerQ*r_,s_]:=eps[Sign[n]*r,s]^Abs[n]/;Abs[n]!=1


(* ::Input::Initialization:: *)
eps[Times[n_?IntegerQ,r_],Times[m_?IntegerQ,r_]]:=(-1)^(1/2 m*n*sp[r,r])


(* ::Text:: *)
(*Define the case eps(r,r).*)


(* ::Input::Initialization:: *)
eps[r_,Times[m_?IntegerQ,r_]]:=(-1)^(1/2 m*sp[r,r])
eps[Times[n_?IntegerQ,r_],r_]:=(-1)^(1/2 n*sp[r,r])
eps[r_,r_]:=(-1)^(1/2 sp[r,r])
eps[0,r_]:=1
eps[r_,0]:=1


(* ::Text:: *)
(*We derive all general cases from (2.80) - (2.87) of [1]*)


(* ::Input::Initialization:: *)
eps[s,r]=eps[r,s];
eps[s,-r]=eps[r,s];
eps[-s,r]=eps[r,s];
eps[-s,-r]=eps[r,s];
eps[s,d]=eps[d,s];
eps[-s,d]=eps[d,s];
eps[s,-d]=eps[d,s];
eps[-s,-d]=eps[d,s];
eps[r,d]=-eps[d,r];
eps[r,-d]=-eps[d,r];
eps[-r,d]=-eps[d,r];
eps[-r,-d]=-eps[d,r];


(* ::Input::Initialization:: *)
eps[-d, -r] = eps[d, r];
eps[-d, r] = eps[d, r];
eps[-d, -r] = eps[d, r];
eps[-d, -s] = eps[d, s];
eps[-d, s] = eps[d, s];
eps[d, -s] = eps[d, s];
eps[-r, -s] = eps[r, s];
eps[-r, s] = eps[r, s];
eps[-r, -s] = eps[r, s];


(* ::Text:: *)
(*And subsequently we set the conventions*)


(* ::Input::Initialization:: *)
eps[d, r]=1;
eps[d,s] = 1;
eps[r, s] =1;


(* ::Text:: *)
(*Since the cocycle factor only assumes the values +1 or -1 we can simplify powers. *)
(*These functions are unused at the moment.*)


(* ::Input::Initialization:: *)
(*epsSimp[f_+g_]:=epsSimp[f]+epsSimp[g]*)


(* ::Input::Initialization:: *)
(*epsSimp[n_?NumericQ*f_]:=n*epsSimp[f]*)


(* ::Input::Initialization:: *)
(*epsSimp[a_.*eps[b_,c_]^n_]:=If[EvenQ[n],a,a*eps[b,c]]*)


(* ::Input::Initialization:: *)
(*epsSimp[f_]:=f*)


(* ::Section:: *)
(*Tachyonic Momenta*)


(* ::Text:: *)
(*Give the general formula for the tachyonic momenta a[l,n].*)


(* ::Input::Initialization:: *)
a[l_,n_]:=-l*r-(l+(n^2-1)/l)d+n*s


(* ::Section:: *)
(*DDF Operators*)


(* ::Text:: *)
(*Transversal DDF Operators of level l and mode m as defined in (3.2) of [1].*)
(*opA acts on a nested product of other DDF operators and a tachyonic state.*)


(* ::Input::Initialization:: *)
opA[l_,m_]:=Function[ddfCom[Sqrt[2]^-1 tp[prod[{s[-1]}],exp[m/l*d]],#]]


(* ::Text:: *)
(*Longitudinal  DDF Operators opB as defined in (3.44) of [1].*)


(* ::Input::Initialization:: *)
opB[l_,m_]:=Function[ddfCom[longitudinalVirasoroOp[l,m],#]]


(* ::Section:: *)
(*Virasoro Operator*)


(* ::Text:: *)
(*Define the Virasoro operator virasoroOp.*)


(* ::Input::Initialization:: *)
virasoroOp[m_]:=Function[virasoroOpAction[m,Expand[#]]]


(* ::Text:: *)
(*Make virasoroOpAction action linear.*)


(* ::Input::Initialization:: *)
virasoroOpAction[m_, Plus[a_,b_]] := virasoroOpAction[m, a]+virasoroOpAction[m,b]


(* ::Input::Initialization:: *)
virasoroOpAction[m_,Times[a_, Plus[b_,c_]]] := virasoroOpAction[m, a*b]+virasoroOpAction[m,a*c]


(* ::Input::Initialization:: *)
virasoroOpAction[m_, a_*tp[b__]] := a*virasoroOpAction[m, tp[b]]


(* ::Text:: *)
(*For mode number -1 the definition is given in (2.108) and (2.109) of [1].*)


(* ::Input::Initialization:: *)
virasoroOpAction[-1,tp[prod[ls_],exp[t_]]]:=Sum[-ls[[k]][[1]]*tp[prod[Sort[Flatten[{ls[[k,0]][ls[[k,1]]-1],Delete[ls,k]}]]],exp[t]],{k,Length[ls]}]+tp[prod[Sort[Flatten[{ls,applyList[toList[t],-1]}]]],exp[t]]


(* ::Input::Initialization:: *)
virasoroOpAction[-1,exp[t_]]:=tp[prod[Sort[{applyList[toList[t],-1]}]],exp[t]]


(* ::Text:: *)
(*For mode number 0 the definition is given in (2.112) in [1].*)


(* ::Input::Initialization:: *)
virasoroOpAction[0,tp[prod[ls_],exp[t_]]]:=1/2 sp[t,t]tp[prod[ls],exp[t]]+Sum[-ls[[k,1]]tp[prod[ls],exp[t]],{k,Length[ls]}]


(* ::Text:: *)
(*For positive mode number the definition is given in (2.116) of [1].*)


(* ::Input::Initialization:: *)
virasoroOpAction[m_, tp[prod[ls_], exp[t_]]] :=Sum[UnitStep[-ls[[k,1]]-m-1]*(-ls[[k, 1]])* tp[prod[Sort[Flatten[{ls[[k,0]][m +ls[[k, 1]]],Delete[ls,k]}]]], exp[t]], {k, Length[ls]}]+
Sum[m*KroneckerDelta[m, -ls[[k,1]]]*sp[ls[[k,0]],t]*tp[prod[Delete[ls,k]], exp[t]] , {k, Length[ls]}]+
Sum[UnitStep[k2-k1-1]*ls[[k1, 1]]*ls[[k2, 1]]*KroneckerDelta[m, -ls[[k1, 1]]-ls[[k2, 1]]]*sp[ls[[k1,0]], ls[[k2,0]]]*tp[prod[Delete[ls,{{k1},{k2}}]], exp[t]], {k1, Length[ls]}, {k2, Length[ls]}]/;m>0


(* ::Section:: *)
(*Double Partition*)


(* ::Text:: *)
(*Define a function doublePartition that computes all partitions of i and j for a given n such that n = i + j. Returns a nested list.*)


(* ::Input::Initialization:: *)
doublePartition[mode_]:=Table[{IntegerPartitions[mode-i],IntegerPartitions[i]},{i,0,mode}]


(* ::Section:: *)
(*DDF to Name*)


(* ::Text:: *)
(*Define a function ddfToName that turns ddfProd[{A_-m1, A_-m2, ... }, exp[state]] into the string Am1Am2.*)


(* ::Input::Initialization:: *)
ddfToName[A[level_,m_]]:=StringJoin["A",ToString[-m]]


(* ::Input::Initialization:: *)
ddfToName[B[level_,m_]]:=StringJoin["B",ToString[-m]]


(* ::Input::Initialization:: *)
ddfToNameJoin[ddfProd[ls_,a_]]:=StringJoin[Table[ddfToName[elem],{elem,ls}]]


(* ::Section:: *)
(*File Name Generator*)


(* ::Text:: *)
(*Define a function fileNamesList that generates a list of all file names for the DDF states with a given level, mode and weight.*)


(* ::Input::Initialization:: *)
fileNamesList[level_,mode_,weight_]:=Table[FileNameJoin[{"ddf_states",StringJoin["level_",ToString[level]],StringJoin["mode_",ToString[mode]],StringJoin["l",ToString[level],"m",ToString[mode],"n",If[weight>=0,ToString[weight],StringJoin["m",ToString[-weight]]],"_",name,".txt"]}],{name,nameTable[mode]}]


(* ::Text:: *)
(*The function needs the function nameTable that produces all possible combinations Am_1 ... Am_i Bm_i+1 ... Bm_n such that m_1 + ... + m_n = mode*)


(* ::Input::Initialization:: *)
nameTable[mode_]:=Flatten[Table[APartition[doublePartition[mode][[i]][[1]]][BPartition[doublePartition[mode][[i]][[2]]]],{i,mode+1}]]


(* ::Text:: *)
(*The definition of nameTable is recursive.*)


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


(* ::Section:: *)
(*ddfProd Generator*)


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


(* ::Section:: *)
(*DDF to Manual Evaluation*)


(* ::Text:: *)
(*We define a function manualEval that takes a ddfProd and manually computes its Fock space representation.*)


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
(*DDF Product to Tensor Product*)


(* ::Text:: *)
(*Define a function toTp that turns an arbitrary DDF product ddfProd into a tensor product tp. *)


(* ::Text:: *)
(*Make  toTp  linear .*)


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
(*If  possible toTp  it  will  read  the  result  from  a  file .*)
(*If  the  file  does  not  exist  it  issues  a  warning  and  proceeds  with  a  manual  calculation .*)


(* ::Input::Initialization:: *)
toTp[ddfProd[ls_, exp[t_]]] := Block[{level = sp[d, t], mode = modeNoAdder[ddfProd[ls, exp[t]]], weight = (1/2)*sp[s, t]}, If[level == 1, manualEval[ddfProd[ls, exp[t]]], 
    fileName = FileNameJoin[{"ddf_states",StringJoin["level_", ToString[level]], StringJoin[ "mode_", ToString[mode]],StringJoin["l", ToString[level], "m", ToString[mode], "n", ToString[(1/2)*sp[s, t]], "_", ddfToNameJoin[ddfProd[ls, exp[t]]], ".txt"]}]; 
     If[FileExistsQ[fileName], ToExpression[Import[fileName]], If[mode>2,Message[toTp::nnarg, n]]; manualEval[ddfProd[ls, exp[t]]]]]]


(* ::Input::Initialization:: *)
toTp::nnarg= "Warning the DDF state has not been pre-computed. Switching to manual evaluation. This might take a while.";


(* ::Section:: *)
(*Tensor Product to DDF Product*)


(* ::Text:: *)
(*Define a function toDDF that turns a linear combination of tensor products tp into DDF products ddfProd. *)
(*The function only works if the linear combination of tps is an element of the DDF algebra and if the basis of DDF states into which the tp transform exist in the folder ddf_states.*)
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
toDDF::nfile= "The DDF states for level `1`, mode `2` and weight `3` were not found in the folder ddf_states.";


(* ::Input::Initialization:: *)
toDDF::nddfState= "The expression is not an element of the DDF algebra.";


(* ::Section:: *)
(*Auxiliary Functions for the Sugawara Operator*)


(* ::Text:: *)
(*Define a number of functions that are used in the definition of the Sugawara operator.*)
(*In particular we have auxiliary functions for DDF operators, called auxA, which will be transformed into normal ordered ddfProdHold expressions.*)
(*Moreover, for the definitions on the DDF tensor products we have auxiliary functions for the affine generators. These must also be normal ordered*)


(* ::Text:: *)
(*Define the roots of unity.*)


(* ::Input::Initialization:: *)
unitRoot[level_,p_]:=Exp[2\[Pi]*I*p/level]


(* ::Text:: *)
(*Define a formal logarithm to extract the tachyonic momentum from the exponential.*)


(* ::Input::Initialization:: *)
formalLog[exp[a_]]:=a


(* ::Text:: *)
(*Define  a normal ordering on a product of two DDF operators*)


(* ::Input::Initialization:: *)
normalOrdering[ddfProdHold[{A[level_,a_],A[level_,b_]}]]:=If[a>b,ddfProdHold[{A[level,b],A[level,a]}],ddfProdHold[{A[level,a],A[level,b]}]]


(* ::Text:: *)
(*Define  a normal ordering on a product of two affine generators*)


(* ::Input::Initialization:: *)
normalOrdering[affineOps[auxH[a_],auxH[b_]]]:=If[a>b,affineOps[auxH[b],auxH[a]],affineOps[auxH[a],auxH[b]]]


(* ::Input::Initialization:: *)
normalOrdering[affineOps[auxE[a_],auxF[b_]]]:=If[a>b,affineOps[auxF[b],auxE[a]],affineOps[auxE[a],auxF[b]]]


(* ::Input::Initialization:: *)
normalOrdering[affineOps[auxF[a_],auxE[b_]]]:=If[a>b,affineOps[auxE[b],auxF[a]],affineOps[auxF[a],auxE[b]]]


(* ::Text:: *)
(*Define  a cutoff function for annihilation operators*)


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


(* ::Section:: *)
(*Transform Product of auxA to ddfProdHold*)


(* ::Text:: *)
(*Define a function transformAuxA that transforms the product of auxA[l,n] functions into a ddfProdHold*)


(* ::Text:: *)
(*Make transformAuxA linear.*)


(* ::Input::Initialization:: *)
transformAuxA[0,ls_]:=0


(* ::Input::Initialization:: *)
transformAuxA[Plus[f_,g_],ls_]:=transformAuxA[f,ls]+transformAuxA[g,ls]


(* ::Input::Initialization:: *)
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
(*Deal with the operator Q.*)


(* ::Input::Initialization:: *)
transformAuxA[f_*auxQ[n_],ls_]:=f*ddfProdHold[Prepend[Sort[ls],Q[n]]]/;FreeQ[f,auxA[__]]


(* ::Input::Initialization:: *)
transformAuxA[auxQ[n_],ls_]:=ddfProdHold[Prepend[Sort[ls],Q[n]]]


(* ::Text:: *)
(*Define trivial case.*)


(* ::Input::Initialization:: *)
transformAuxA[f_,ls_]:=f*ddfProdHold[Sort[ls]]/;FreeQ[f,auxA[__]]&&FreeQ[f,auxQ[_]]


(* ::Section:: *)
(*Sugawara Schur Polynomials*)


(* ::Text:: *)
(*Define the Schur polynomials sugawaraSchurEval used in the definition of the Sugawara operator.*)


(* ::Text:: *)
(*The first 11 Schur polynomials are defined explicitly.*)


(* ::Input::Initialization:: *)
sugawaraSchurEval[0,level_,p_,sgn_]:=1


(* ::Input::Initialization:: *)
sugawaraSchurEval[1,level_,p_,sgn_]:=Sqrt[2] sgn auxA[level,-1]-Sqrt[2] sgn auxA[level,-1] unitRoot[level,p]


(* ::Input::Initialization:: *)
sugawaraSchurEval[2,level_,p_,sgn_]:=(sgn auxA[level,-2])/Sqrt[2]+auxA[level,-1]^2-2 auxA[level,-1]^2 unitRoot[level,p]-(sgn auxA[level,-2] unitRoot[level,p]^2)/Sqrt[2]+auxA[level,-1]^2 unitRoot[level,p]^2


(* ::Text:: *)
(*The longer definitions are read from files.*)


(* ::Input::Initialization:: *)
Get[FileNameJoin[{"schur_polynomials","sugawara_schur_3.wls"}]]


(* ::Input::Initialization:: *)
Get[FileNameJoin[{"schur_polynomials","sugawara_schur_4.wls"}]]


(* ::Input::Initialization:: *)
Get[FileNameJoin[{"schur_polynomials","sugawara_schur_5.wls"}]]


(* ::Input::Initialization:: *)
Get[FileNameJoin[{"schur_polynomials","sugawara_schur_6.wls"}]]


(* ::Input::Initialization:: *)
Get[FileNameJoin[{"schur_polynomials","sugawara_schur_7.wls"}]]


(* ::Input::Initialization:: *)
Get[FileNameJoin[{"schur_polynomials","sugawara_schur_8.wls"}]]


(* ::Input::Initialization:: *)
Get[FileNameJoin[{"schur_polynomials","sugawara_schur_9.wls"}]]


(* ::Input::Initialization:: *)
Get[FileNameJoin[{"schur_polynomials","sugawara_schur_10.wls"}]]


(* ::Text:: *)
(*For n > 10 the Schur polynomials are calculated at runtime.*)


(* ::Input::Initialization:: *)
sugawaraSchurEval[n_,level_,p_,sgn_]:=Block[{},Message[sugawaraSchurEval::nnarg];
ExpandAll[SeriesCoefficient[Series[Exp[Sum[sgn/j*(Sqrt[2]auxA[level,-j](1-Power[unitRoot[level,p],j]))*z^j,{j,1,n}]],{z,0,n}],n]]]/;n>10


(* ::Input::Initialization:: *)
sugawaraSchurEval::nnarg= "The Schur polynomial necessary for this calculation has not been pre-computed. Switching to manual evaluation. This might increase the calculation time.";


(* ::Section:: *)
(*Sugawara Operator*)


(* ::Text:: *)
(*Formally define the Sugawara operator sugawaraOp as a function.*)
(*The definition of sugawaraOpAction is given below.*)


(* ::Input::Initialization:: *)
sugawaraOp[m_]:=Function[Block[{expr=Expand[#]},If[expr==0,Return[0,Block]];
Block[{ddfProperties=ddfProdInvestigator[expr]},sugawaraOpAction[ddfProperties[[1]],ddfProperties[[2]],m,expr]]]]


(* ::Section:: *)
(*Sugawara Operator Action*)


(* ::Text:: *)
(*We define the action of the Sugawara operator as the sum of its four terms. *)
(*The precise definition of the Sugawara operator is taken from (3.27) of [2].*)


(* ::Text:: *)
(*Make  sugawaraOpAction  linear .*)


(* ::Input::Initialization:: *)
sugawaraOpAction[args__,m_,Plus[state1_,state2_]]:=sugawaraOpAction[args,m,state1]+sugawaraOpAction[args,m,state2]


(* ::Input::Initialization:: *)
sugawaraOpAction[args__,m_,n_*ddfProd[ddf_,tachyon_]]:=n*sugawaraOpAction[args,m,ddfProd[ddf,tachyon]]


(* ::Input::Initialization:: *)
sugawaraOpAction[args__,m_,eps[a_,b_]*state_]:=eps[a,b]*sugawaraOpAction[args,m,state]


(* ::Input::Initialization:: *)
sugawaraOpAction[args__,m_,0]:=0


(* ::Text:: *)
(*Define the action on a tachyonic state*)


(* ::Input::Initialization:: *)
sugawaraOpAction[args__,m_,exp[tachyon_]]:=sugawaraOpAction[args,m,ddfProd[{},exp[tachyon]]]


(* ::Input::Initialization:: *)
sugawaraOpAction[args__,m_,n_*exp[tachyon_]]:=n*sugawaraOpAction[args,m,ddfProd[{},exp[tachyon]]]


(* ::Text:: *)
(*Define the action on a single ddfProd as the sum of the action of four terms.*)


(* ::Input::Initialization:: *)
sugawaraOpAction[level_,modeSum_,m_,ddfProd[ddf_,tachyon_]]:=firstTerm[level,m,modeSum,ddfProd[ddf,tachyon]]+secondTerm[level,m,modeSum,ddfProd[ddf,tachyon]]+thirdTerm[level,m,modeSum,tachyon,ddfProd[ddf,tachyon]]+fourthTerm[level,m,modeSum,tachyon,ddfProd[ddf,tachyon]]


(* ::Text:: *)
(*The four terms are defined as follow:*)
(*1st Term*)


(* ::Input::Initialization:: *)
firstTerm[level_,m_,mode_,ddfProd[ddf_,tachyon_]]:=1/(2*level) joinProd[Sum[cutoff[normalOrdering[ddfProdHold[{A[level,level*k],A[level,level(m-k)]}]],mode],{k,-Infinity,Infinity}],ddfProd[ddf,tachyon]]


(* ::Text:: *)
(*2nd Term*)


(* ::Input::Initialization:: *)
secondTerm[1,m_,mode_,ddfProd[ddf_,tachyon_]]:=0


(* ::Input::Initialization:: *)
secondTerm[level_,m_,mode_,ddfProd[ddf_,tachyon_]]:=1/(level(level+2)) joinProd[Sum[(1-KroneckerDelta[0,Mod[k,level]])cutoff[normalOrdering[ddfProdHold[{A[level,k],A[level,level*m-k]}]],mode],{k,-Infinity,Infinity}],ddfProd[ddf,tachyon]]/;level>1


(* ::Text:: *)
(*3rd Term*)


(* ::Input::Initialization:: *)
thirdTerm[1,m_,mode_,exp[state_],ddfProd[ddf_,tachyon_]]:=0


(* ::Input::Initialization:: *)
thirdTerm[level_,m_,mode_,exp[state_],ddfProd[ddf_,tachyon_]]:=0/;m!=0


(* ::Input::Initialization:: *)
thirdTerm[level_,0,mode_,exp[state_],ddfProd[ddf_,tachyon_]]:=((Mod[sp[s,state],level]*(level-Mod[sp[s,state],level]))/(4*level(level+2))+(Mod[sp[-s,state],level]*(level-Mod[sp[-s,state],level]))/(4*level(level+2)))*joinProd[ddfProdHold[{}],ddfProd[ddf,tachyon]]/;level>1


(* ::Text:: *)
(*4th Term*)


(* ::Input::Initialization:: *)
fourthTerm[1,m_,mode_,exp[state_],ddfProd[ddf_,tachyon_]]:=0


(* ::Input::Initialization:: *)
fourthTerm[level_,m_,mode_,exp[state_],ddfProd[ddf_,tachyon_]]:=joinProd[transformAuxA[ReplaceAll[sumResExp[level,m,mode,-1,exp[state]],sugawaraSchur->sugawaraSchurEval],{}]+transformAuxA[ReplaceAll[sumResExp[level,m,mode,1,exp[state]],sugawaraSchur->sugawaraSchurEval],{}],ddfProd[ddf,tachyon]]/;level>1


(* ::Input::Initialization:: *)
sumResExp[level_, m_, mode_, sgn_, exp[state_]] :=  -(Sum[(unitRoot[level, p]^(-sgn*sp[s, state])*Coefficient[Sum[sugawaraSchur[k,level,p,sgn]*z^k, {k, 0, 100}]*(1 + Sum[Sum[Coefficient[Sum[(-sgn*Sqrt[2]*auxA[level, n]*y^n*(1 - unitRoot[level, p]^(-n)))/(z^n*n), {n, 1, mode}]^k, y, i], {i, 0, mode}]/k!, {k, 1, mode}]) - 1, z, (-level)*m])/
      Abs[unitRoot[level, p] - 1]^2, {p, 1, level - 1}]/(2*level*(level + 2)))


(* ::Section:: *)
(*Sugawara Operator for ddfTp*)


(* ::Text:: *)
(*Formally define the Sugawara operator sugawaraOpTp as a function.*)
(*The definition of sugawaraOpTpAction is given below.*)


(* ::Input::Initialization:: *)
sugawaraOpTp[m_]:=Function[Block[{expr=Expand[#]},sugawaraOpTpAction[m,expr]]]


(* ::Text:: *)
(*The ddfTp Properties is a list with with two sublists, one for each of the tp factors.*)
(*The entries in the sublists are level, modeSum and weight of the DDF states*)


(* ::Section:: *)
(*Sugawara Operator Action on ddfTp*)


(* ::Text:: *)
(*Give the precise action of the Sugawara operator sugawaraOpTp on a DDF tensor product*)


(* ::Text:: *)
(*Make the action linear*)


(* ::Input::Initialization:: *)
sugawaraOpTpAction[m_,0]:=0


(* ::Input::Initialization:: *)
sugawaraOpTpAction[m_,Plus[state1_,state2_]]:=sugawaraOpTpAction[m,state1]+sugawaraOpTpAction[m,state2]


(* ::Input::Initialization:: *)
sugawaraOpTpAction[m_,num_*ddfTp[ddf1_,ddf2_]]:=num*sugawaraOpTpAction[m,ddfTp[ddf1,ddf2]]


(* ::Input::Initialization:: *)
sugawaraOpTpAction[m_,eps[a_,b_]*state_]:=eps[a,b]*sugawaraOpTpAction[m,state]


(* ::Text:: *)
(*Give the precise definition according to (3.22) from [2] in terms of affine generators.*)


(* ::Input::Initialization:: *)
sugawaraOpTpAction[m_,ddfTp[ddf1_,ddf2_]]:=Block[{ddfProperties1=ddfProdInvestigator[ddf1],ddfProperties2=ddfProdInvestigator[ddf2]},
Block[{level1=ddfProperties1[[1]],depth1=ddfProperties1[[1]]+(ddfProperties1[[3]]^2-1+ddfProperties1[[2]])/ddfProperties1[[1]],level2=ddfProperties2[[1]],depth2=ddfProperties2[[1]]+(ddfProperties2[[3]]^2-1+ddfProperties2[[2]])/ddfProperties2[[1]]}, 1/(4*(level1+level2+2)) affineAction[Sum[cutoff[normalOrdering[affineOps[auxH[k],auxH[m-k]]],depth1,depth2],{k,-Infinity,Infinity}],ddfTp[ddf1,ddf2]]+1/(2*(level1+level2+2)) affineAction[Sum[cutoff[normalOrdering[affineOps[auxE[k],auxF[m-k]]],depth1,depth2],{k,-Infinity,Infinity}],ddfTp[ddf1,ddf2]]+1/(2*(level1+level2+2)) affineAction[Sum[cutoff[normalOrdering[affineOps[auxF[k],auxE[m-k]]],depth1,depth2],{k,-Infinity,Infinity}],ddfTp[ddf1,ddf2]]]]


(* ::Text:: *)
(*Define one version of the action where the arguments are provided manually*)


(* ::Input::Initialization:: *)
sugawaraOpTpActionPrivate[level1_,depth1_,level2_,depth2_,m_,ddfTp[ddf1_,ddf2_]]:=1/(4*(level1+level2+2)) affineAction[Sum[cutoff[normalOrdering[affineOps[auxH[k],auxH[m-k]]],depth1,depth2],{k,-Infinity,Infinity}],ddfTp[ddf1,ddf2]]+1/(2*(level1+level2+2)) affineAction[Sum[cutoff[normalOrdering[affineOps[auxE[k],auxF[m-k]]],depth1,depth2],{k,-Infinity,Infinity}],ddfTp[ddf1,ddf2]]+1/(2*(level1+level2+2)) affineAction[Sum[cutoff[normalOrdering[affineOps[auxF[k],auxE[m-k]]],depth1,depth2],{k,-Infinity,Infinity}],ddfTp[ddf1,ddf2]]


(* ::Section:: *)
(*Coset Virasoro Operator*)


(* ::Text:: *)
(*Define the coset Virasoro operator that acts on a ddfTp. It takes the mode as an argument.*)
(*There is no coset Virasoro operator that acts on commutators.*)


(* ::Input::Initialization:: *)
cosetVirasoroOpTp[m_]:=Function[Block[{expr=Expand[#]},cosetVirasoroOpTpAction[m,expr]]]


(* ::Text:: *)
(*Define the action for cosetVirasoroOpTpAction*)


(* ::Input::Initialization:: *)
cosetVirasoroOpTpAction[m_,0]:=0


(* ::Input::Initialization:: *)
cosetVirasoroOpTpAction[m_,Plus[state1_,state2_]]:=cosetVirasoroOpTpAction[m,state1]+cosetVirasoroOpTpAction[m,state2]


(* ::Input::Initialization:: *)
cosetVirasoroOpTpAction[m_,num_*ddfTp[ddf1_,ddf2_]]:=num*cosetVirasoroOpTpAction[m,ddfTp[ddf1,ddf2]]


(* ::Input::Initialization:: *)
cosetVirasoroOpTpAction[m_,eps[a_,b_]*state_]:=eps[a,b]*cosetVirasoroOpTpAction[m,state]


(* ::Input::Initialization:: *)
cosetVirasoroOpTpAction[m_,ddfTp[ddf1_,ddf2_]]:=Block[{ddfProperties1=ddfProdInvestigator[ddf1],ddfProperties2=ddfProdInvestigator[ddf2]},
Block[{level1=ddfProperties1[[1]],modeSum1=ddfProperties1[[2]],depth1=ddfProperties1[[1]]+(ddfProperties1[[3]]^2-1+ddfProperties1[[2]])/ddfProperties1[[1]],
level2=ddfProperties2[[1]],modeSum2=ddfProperties2[[2]],depth2=ddfProperties2[[1]]+(ddfProperties2[[3]]^2-1+ddfProperties2[[2]])/ddfProperties2[[1]]},
ddfTp[sugawaraOpAction[level1,modeSum1,m,ddf1],ddf2]+ddfTp[ddf1,sugawaraOpAction[level2,modeSum2,m,ddf2]]-sugawaraOpTpActionPrivate[level1,depth1,level2,depth2,m,ddfTp[ddf1,ddf2]]]]


(* ::Section:: *)
(*Affine Operators*)


(* ::Text:: *)
(*Define a auxiliary function that keeps track of the auxiliary affine generators*)


(* ::Input::Initialization:: *)
affineOps[Plus[expr1_,expr2_],expr3_]:=affineOps[expr1,expr3]+affineOps[expr2,expr3]


(* ::Input::Initialization:: *)
affineOps[expr1_,Plus[expr2_,expr3_]]:=affineOps[expr1,expr2]+affineOps[expr1,expr3]


(* ::Input::Initialization:: *)
affineOps[Times[n_*Plus[expr1_,expr2_]],expr3_]:=affineOps[n*expr1,expr3]+affineOps[n*expr2,expr3]


(* ::Input::Initialization:: *)
affineOps[expr1_,Times[n_*Plus[expr2_,expr3_]]]:=affineOps[expr1,n*expr2]+affineOps[expr1,n*expr3]


(* ::Input::Initialization:: *)
affineOps[f_*auxH[m_],expr1_]:=f*affineOps[auxH[m],expr1]


(* ::Input::Initialization:: *)
affineOps[f_*auxE[m_],expr1_]:=f*affineOps[auxE[m],expr1]


(* ::Input::Initialization:: *)
affineOps[f_*auxF[m_],expr1_]:=f*affineOps[auxF[m],expr1]


(* ::Input::Initialization:: *)
affineOps[expr1_,f_*auxH[m_]]:=f*affineOps[expr1,auxH[m]]


(* ::Input::Initialization:: *)
affineOps[expr1_,f_*auxE[m_]]:=f*affineOps[expr1,auxE[m]]


(* ::Input::Initialization:: *)
affineOps[expr1_,f_*auxF[m_]]:=f*affineOps[expr1,auxF[m]]


(* ::Section:: *)
(*Affine Schur Polynomials*)


(* ::Text:: *)
(*Define the Schur polynomials used in the definitions of the affine generators.*)


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
Get[FileNameJoin[{"schur_polynomials","affine_schur_5.wls"}]]


(* ::Input::Initialization:: *)
Get[FileNameJoin[{"schur_polynomials","affine_schur_6.wls"}]]


(* ::Input::Initialization:: *)
Get[FileNameJoin[{"schur_polynomials","affine_schur_7.wls"}]]


(* ::Input::Initialization:: *)
Get[FileNameJoin[{"schur_polynomials","affine_schur_8.wls"}]]


(* ::Input::Initialization:: *)
Get[FileNameJoin[{"schur_polynomials","affine_schur_9.wls"}]]


(* ::Input::Initialization:: *)
Get[FileNameJoin[{"schur_polynomials","affine_schur_10.wls"}]]


(* ::Input::Initialization:: *)
Get[FileNameJoin[{"schur_polynomials","affine_schur_11.wls"}]]


(* ::Input::Initialization:: *)
Get[FileNameJoin[{"schur_polynomials","affine_schur_12.wls"}]]


(* ::Text:: *)
(*For n > 12 the Schur polynomials have not been pre-computed. The following function will compute them at runtime and issue a warning that this might delay the evaluation.*)


(* ::Input::Initialization:: *)
affineSchurEval[n_,level_,sgn_]:=Block[{},Message[affineSchurEval::nnarg];
ExpandAll[SeriesCoefficient[Series[Exp[Sum[sgn/j*(Sqrt[2]auxA[level,-j])*z^j,{j,1,n}]],{z,0,n}],n]]]


(* ::Input::Initialization:: *)
affineSchurEval::nnarg= "The Schur polynomial necessary for this calculation has not been pre-computed. Switching to manual evaluation. This might increase the calculation time.";


(* ::Section:: *)
(*Affine Generators*)


(* ::Text:: *)
(*Formally define the affine generators as functions.*)
(*Find out level and mode sum according to input.*)
(*The definition of affineActionH,  affineActionE and affineActionF are given below.*)


(* ::Input::Initialization:: *)
affineH[m_]:=Function[Block[{expr=Expand[#]},affineActionH[m,expr]]]


(* ::Input::Initialization:: *)
affineE[m_]:=Function[Block[{expr=Expand[#]},affineActionE[m,expr]]]


(* ::Input::Initialization:: *)
affineF[m_]:=Function[Block[{expr=Expand[#]},affineActionF[m,expr]]]


(* ::Section:: *)
(*Affine Action*)


(* ::Text:: *)
(*We define the affine actions. They are all linear functions.*)


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


(* ::Text:: *)
(*The generator H is defined as H_m = Sqrt[2]  l A_lm.*)


(* ::Input::Initialization:: *)
affineActionH[m_,0]:=0


(* ::Input::Initialization:: *)
affineActionH[m_,exp[tachyon_]]:=affineActionH[m,ddfProd[{},exp[tachyon]]]


(* ::Input::Initialization:: *)
affineActionH[m_,n_*exp[tachyon_]]:=n*affineActionH[m,ddfProd[{},exp[tachyon]]]


(* ::Input::Initialization:: *)
affineActionH[m_,ddfProd[ddf_,tachyon_]]:=Block[{level=ddfProdInvestigator[ddfProd[ddf,tachyon]][[1]]},Sqrt[2]*joinProd[ddfProdHold[{A[level,level*m]}],ddfProd[ddf,tachyon]]]


(* ::Input::Initialization:: *)
affineActionH[m_,ddfTp[ddf1_,ddf2_]]:=ddfTp[affineActionH[m,ddf1],ddf2]+ddfTp[ddf1,affineActionH[m,ddf2]]


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


(* ::Text:: *)
(*The precise definition of E_m is taken from page 8 of [2].*)


(* ::Input::Initialization:: *)
affineActionE[m_,0]:=0


(* ::Input::Initialization:: *)
affineActionE[m_,exp[tachyon_]]:=affineActionE[m,ddfProd[{},exp[tachyon]]]


(* ::Input::Initialization:: *)
affineActionE[m_,n_*exp[tachyon_]]:=n*affineActionE[m,ddfProd[{},exp[tachyon]]]


(* ::Input::Initialization:: *)
affineActionE[m_,ddfProd[ddf_,exp[tachyon_]]]:=Block[{ddfProperties=ddfProdInvestigator[ddfProd[ddf,exp[tachyon]]]},Block[{level=ddfProperties[[1]],modeSum=ddfProperties[[2]]},eps[s,tachyon-modeSum/level*d] joinProd[transformAuxA[ReplaceAll[expQPexp[level,m,modeSum,1,exp[tachyon]], affineSchur->affineSchurEval],{}],ddfProd[ddf,exp[tachyon]]]]]


(* ::Input::Initialization:: *)
affineActionE[m_,ddfTp[ddf1_,ddf2_]]:=ddfTp[affineActionE[m,ddf1],ddf2]+ddfTp[ddf1,affineActionE[m,ddf2]]


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


(* ::Text:: *)
(*The  precise  definition  of  E=F_m  is  taken  from  page  8  of [2] .*)


(* ::Input::Initialization:: *)
affineActionF[m_,0]:=0


(* ::Input::Initialization:: *)
affineActionF[m_,exp[tachyon_]]:=affineActionF[m,ddfProd[{},exp[tachyon]]]


(* ::Input::Initialization:: *)
affineActionF[m_,n_*exp[tachyon_]]:=n*affineActionF[m,ddfProd[{},exp[tachyon]]]


(* ::Input::Initialization:: *)
affineActionF[m_,ddfProd[ddf_,exp[tachyon_]]]:=Block[{ddfProperties=ddfProdInvestigator[ddfProd[ddf,exp[tachyon]]]},Block[{level=ddfProperties[[1]],modeSum=ddfProperties[[2]]},-eps[-s,tachyon-modeSum/level*d]joinProd[transformAuxA[ReplaceAll[expQPexp[level,m,modeSum,-1,exp[tachyon]],affineSchur->affineSchurEval],{}],ddfProd[ddf,exp[tachyon]]]]]


(* ::Input::Initialization:: *)
affineActionF[m_,ddfTp[ddf1_,ddf2_]]:=ddfTp[affineActionF[m,ddf1],ddf2]+ddfTp[ddf1,affineActionF[m,ddf2]]


(* ::Text:: *)
(*Give the definition of the exponential function used.*)


(* ::Input::Initialization:: *)
expQPexp[level_, m_, mode_, sgn_, exp[state_]] := auxQ[sgn]*Coefficient[Sum[affineSchur[k, level, sgn]*z^k, {k, 0, 20}]*(1 + Sum[1/k!*Sum[Coefficient[Sum[-sgn/n*(Sqrt[2]*auxA[level, n]*y^n)*z^(-n), {n, 1, mode}]^k, y, i], {i, 0, mode}], {k, 1, mode}]), z, Expand[-1-level*m-sgn*sp[s, state]]]


(* ::Section:: *)
(*Affine Action for Auxiliary Functions*)


(* ::Text:: *)
(*Define the double affine action on the auxiliary functions*)


(* ::Input::Initialization:: *)
affineAction[0,ddfTp[ddf1_,ddf2_]]:=0


(* ::Input::Initialization:: *)
affineAction[Plus[expr1_,expr2_],ddfTp[ddf1_,ddf2_]]:=affineAction[expr1,ddfTp[ddf1,ddf2]]+affineAction[expr2,ddfTp[ddf1,ddf2]]


(* ::Input::Initialization:: *)
affineAction[Times[n_*Plus[expr1_,expr2_]],ddfTp[ddf1_,ddf2_]]:=affineAction[n*expr1,ddfTp[ddf1,ddf2]]+affineAction[n*expr2,ddfTp[ddf1,ddf2]]


(* ::Input::Initialization:: *)
affineAction[n_*affineOps[expr1_,expr2_],ddfTp[ddf1_,ddf2_]]:=n*affineAction[affineOps[expr1,expr2],ddfTp[ddf1,ddf2]]


(* ::Input::Initialization:: *)
affineAction[affineOps[auxH[m1_],auxH[m2_]],ddfTp[ddf1_,ddf2_]]:=affineH[m1][affineH[m2][ddfTp[ddf1,ddf2]]]


(* ::Input::Initialization:: *)
affineAction[affineOps[auxE[m1_],auxF[m2_]],ddfTp[ddf1_,ddf2_]]:=affineE[m1][affineF[m2][ddfTp[ddf1,ddf2]]]


(* ::Input::Initialization:: *)
affineAction[affineOps[auxF[m1_],auxE[m2_]],ddfTp[ddf1_,ddf2_]]:=affineF[m1][affineE[m2][ddfTp[ddf1,ddf2]]]


(* ::Section:: *)
(*Multi-Commutator*)


(* ::Text:: *)
(*Define the Chevalley-Serre Generators*)


(* ::Input::Initialization:: *)
e[-1]=exp[r];
e[0]=exp[d-s];
e[1]=exp[s];


(* ::Input::Initialization:: *)
f[-1]=-exp[-r];
f[0]=-exp[-d+s];
f[1]=-exp[-s];


(* ::Input::Initialization:: *)
h[-1]=tp[prod[{r[-1]}],exp[0]];
h[0]=tp[prod[{d[-1]}],exp[0]]-tp[prod[{s[-1]}],exp[0]];
h[1]=tp[prod[{s[-1]}],exp[0]];


(* ::Text:: *)
(*Define the multi-commutator multiCom*)
(*multiCom takes two or more arguments.*)
(*At first the last argument is -1, 0 or 1. Define this case*)


(* ::Input::Initialization:: *)
multiCom[ls__,-1]:=multiComRecursive[ls,f[-1]]


(* ::Input::Initialization:: *)
multiCom[ls__,0]:=multiComRecursive[ls,f[0]]


(* ::Input::Initialization:: *)
multiCom[ls__,1]:=multiComRecursive[ls,f[1]]


(* ::Text:: *)
(*Give the recursive definition.*)


(* ::Input::Initialization:: *)
multiComRecursive[ls__,last_]:=multiComRecursive[Apply[Sequence,Drop[{ls},-1]],com[f[Last[{ls}]],last]]


(* ::Text:: *)
(*Define end case*)


(* ::Input::Initialization:: *)
multiComRecursive[expr_]:=sortProd[expr//ExpandAll]


(* ::Section:: *)
(*End Package*)


(* ::Input::Initialization:: *)
Print["Successfully loaded the DDF package."];


(* ::Input::Initialization:: *)
Print["All equations and relations used in this package are derived from the papers [1,2] and appropriately adjusted to the Feingold-Frenkel algebra F."];


(* ::Input::Initialization:: *)
Print["[1] R.W. Gebert and H. Nicolai, On E(10) and the DDF construction, Commun. Math. Phys. 172 (1995), 571-622, arXiv:hep-th/9406175."];


(* ::Input::Initialization:: *)
Print["[2] R.W. Gebert and H. Nicolai, An Affine string vertex operator construction at arbitrary level, J. Math. Phys. 38 (1997), 4435-4450, arXiv:hep-th/9608014."];


(* ::Input::Initialization:: *)
Print[""];


(* ::Input::Initialization:: *)
Print["Copyright (C) 2024, Hannes Malcha"];


(* ::Input::Initialization:: *)
End[]


(* ::Input::Initialization:: *)
EndPackage[]


(* ::Input::Initialization:: *)
Protect["ddf`*"];
