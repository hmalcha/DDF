(* ::Package:: *)

(* ::Title:: *)
(*Fock States*)


(* ::Text:: *)
(*This file is part of the DDF Mathematica Package.*)


(* ::Text:: *)
(*Copyright \[Copyright] 2025 Hannes Malcha*)


(* ::Text:: *)
(*The DDF Package is free software: you can redistribute it and/or modify it under the terms of the GNU General Public License as published by the Free Software Foundation, either version 3 of the License, or (at your option) any later version.*)
(*The DDF Package is distributed in the hope that it will be useful, but WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the GNU General Public License for more details.*)
(*You should have received a copy of the GNU General Public License along with the DDF Package. If not, see https://www.gnu.org/licenses/.*)


(* ::Text:: *)
(*This module introduces the elements of the Fock space  \[ScriptCapitalF] on which the vertex operator algebra acts.*)


(* ::Text:: *)
(*Elements of the Fock space are called Fock states. They are linear combinations of tensor products of elements from the vector space of finite products of creation operators S(h^-) and the twisted group algebra \[DoubleStruckCapitalR]{\[CapitalLambda]}. *)


(* ::Text:: *)
(*We introduce a custom function tp[prod[...], exp[...]] for the tensor product of elements from the vector space of finite products of creation operators and the twisted group algebra. The first argument of tp is the product and the second argument is the twisted group algebra element. *)


(* ::Text:: *)
(*The argument of prod[...] is a list of r[m], s[m] and d[m]. The argument of exp[...] is a linear combination of r, s and t. The wrapper functions prod is necessary to implement the vertex operator algebra on the Fock states.*)


(* ::Text:: *)
(*Finally, this module also introduces the Virasoro operator that acts on Fock states.*)


(* ::Section:: *)
(*Public Functions and Symbols from this Module*)


(* ::Text:: *)
(*prod*)
(*exp*)
(*tp*)
(*sortProd*)
(*virasoroOp*)


(* ::Section:: *)
(*Product on the Vector Space of Roots*)


(* ::Text:: *)
(*We define the formal product on the vector space of roots.*)


(* ::Text:: *)
(*The empty product is equal to 1.*)


(* ::Input::Initialization:: *)
prod[{}]:=1


(* ::Text:: *)
(*A product containing a zero is zero.*)


(* ::Input::Initialization:: *)
prod[{___,0,___}]:=0


(* ::Text:: *)
(*Make prod multi-linear; but not on formal sums.*)


(* ::Input::Initialization:: *)
prod[{ls1___,Plus[a_,b_],ls2___}]:=prod[{ls1,a,ls2}]+prod[{ls1,b,ls2}]
prod[{ls1___,Times[n_?NumericQ,a_],ls2___}]:=n*prod[{ls1,a,ls2}]


(* ::Section:: *)
(*The Tensor Product*)


(* ::Text:: *)
(*Make the tensor product linear in the first argument.*)


(* ::Input::Initialization:: *)
tp[n_?NumericQ*a_,exp[t_]]:=n*tp[a,exp[t]]


(* ::Input::Initialization:: *)
tp[Plus[a_,b_],exp[t_]]:=tp[a,exp[t]]+tp[b,exp[t]]


(* ::Input::Initialization:: *)
tp[Times[a_,Plus[b_,c_]],exp[t_]]:=tp[a*b,exp[t]]+tp[a*c,exp[t]]


(* ::Text:: *)
(*For the implementation of the vertex operator algebra it is important to take out the loop variables from the tensor product.*)


(* ::Input::Initialization:: *)
tp[z^m_.*a_,exp[t_]]:=z^m*tp[a,exp[t]]


(* ::Text:: *)
(*Define the trivial cases.*)


(* ::Input::Initialization:: *)
tp[0,_]:=0


(* ::Input::Initialization:: *)
tp[1,exp[t_]]:=exp[t]


(* ::Text:: *)
(*Extend the linearity to formal sums.*)


(* ::Input::Initialization:: *)
tp[a_.*Sum[b_,limits__],exp[t_]]:=Sum[tp[a*b,exp[t]],limits]


(* ::Text:: *)
(*Concatenate products in the first argument of the tensor product. *)


(* ::Input::Initialization:: *)
tp[a_.*prod[{ls1__}]*prod[{ls2__}],exp[t_]]:=tp[a*prod[Sort[{ls1,ls2}]],exp[t]]


(* ::Input::Initialization:: *)
tp[a_.*prod[{ls1__}]^n_,exp[t_]]:=tp[a*prod[Sort[Flatten[Table[{ls1},n]]]],exp[t]]


(* ::Section:: *)
(*Sort Products*)


(* ::Text:: *)
(*Bring the first argument of a tensor product into a canonical order.*)


(* ::Input::Initialization:: *)
sortProd[f_+g_]:=sortProd[f]+sortProd[g]
sortProd[n_?NumericQ*f_]:=n*sortProd[f]
sortProd[f_*tp[g__]]:=f*sortProd[tp[g]]
sortProd[eps[a_,b_]*c_]:=eps[a,b]*sortProd[c]
sortProd[f_]:=f


(* ::Input::Initialization:: *)
sortProd[tp[prod[ls_],g_]]:=tp[prod[Sort[ls]],g]


(* ::Section:: *)
(*Virasoro Operator*)


(* ::Text:: *)
(*Functional definition of the Virasoro operator*)


(* ::Input::Initialization:: *)
virasoroOp[m_]:=Function[virasoroOpAction[m,Expand[#]]]


(* ::Text:: *)
(*Make virasoroOpAction linear.*)


(* ::Input::Initialization:: *)
virasoroOpAction[m_, Plus[a_,b_]] := virasoroOpAction[m, a]+virasoroOpAction[m,b]


(* ::Input::Initialization:: *)
virasoroOpAction[m_,Times[a_, Plus[b_,c_]]] := virasoroOpAction[m, a*b]+virasoroOpAction[m,a*c]


(* ::Input::Initialization:: *)
virasoroOpAction[m_, a_*tp[b__]] := a*virasoroOpAction[m, tp[b]]


(* ::Text:: *)
(*For m = -1 the definition of the Virasoro operator is given in (2.108) and (2.109) of [1].*)


(* ::Input::Initialization:: *)
virasoroOpAction[-1,tp[prod[ls_],exp[t_]]]:=Sum[-ls[[k]][[1]]*tp[prod[Sort[Flatten[{ls[[k,0]][ls[[k,1]]-1],Delete[ls,k]}]]],exp[t]],{k,Length[ls]}]+tp[prod[Sort[Flatten[{ls,applyList[toList[t],-1]}]]],exp[t]]


(* ::Input::Initialization:: *)
virasoroOpAction[-1,exp[t_]]:=tp[prod[Sort[{applyList[toList[t],-1]}]],exp[t]]


(* ::Text:: *)
(*For m = 0 the definition of the Virasoro operator is given in (2.112) in [1].*)


(* ::Input::Initialization:: *)
virasoroOpAction[0,tp[prod[ls_],exp[t_]]]:=1/2 sp[t,t]tp[prod[ls],exp[t]]+Sum[-ls[[k,1]]tp[prod[ls],exp[t]],{k,Length[ls]}]


(* ::Text:: *)
(*For m > 0 the definition of the Virasoro operator is given in (2.116) of [1].*)


(* ::Input::Initialization:: *)
virasoroOpAction[m_, tp[prod[ls_], exp[t_]]] :=Sum[UnitStep[-ls[[k,1]]-m-1]*(-ls[[k, 1]])* tp[prod[Sort[Flatten[{ls[[k,0]][m +ls[[k, 1]]],Delete[ls,k]}]]], exp[t]], {k, Length[ls]}]+
Sum[m*KroneckerDelta[m, -ls[[k,1]]]*sp[ls[[k,0]],t]*tp[prod[Delete[ls,k]], exp[t]] , {k, Length[ls]}]+
Sum[UnitStep[k2-k1-1]*ls[[k1, 1]]*ls[[k2, 1]]*KroneckerDelta[m, -ls[[k1, 1]]-ls[[k2, 1]]]*sp[ls[[k1,0]], ls[[k2,0]]]*tp[prod[Delete[ls,{{k1},{k2}}]], exp[t]], {k1, Length[ls]}, {k2, Length[ls]}]/;m>0
