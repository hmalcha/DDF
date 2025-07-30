(* ::Package:: *)

(* ::Title:: *)
(*Multi-Commutators*)


(* ::Text:: *)
(*This file is part of the DDF Mathematica Package.*)


(* ::Text:: *)
(*Copyright \[Copyright] 2025 Hannes Malcha*)


(* ::Text:: *)
(*The DDF Package is free software: you can redistribute it and/or modify it under the terms of the GNU General Public License as published by the Free Software Foundation, either version 3 of the License, or (at your option) any later version.*)
(*The DDF Package is distributed in the hope that it will be useful, but WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the GNU General Public License for more details.*)
(*You should have received a copy of the GNU General Public License along with the DDF Package. If not, see https://www.gnu.org/licenses/.*)


(* ::Text:: *)
(*This module introduces the Chevalley-Serre generators e_i, f_i, h_i according to (2.125) - (2.127) of [1].*)
(*The generators are used to obtain a multi-commutator representation on the Feingold-Frenkel algebra.*)


(* ::Section:: *)
(*Public Functions from this Module*)


(* ::Text:: *)
(*e*)
(*f*)
(*h*)
(*cartanMatrix*)
(*multiCom*)


(* ::Section:: *)
(*Chevalley-Serre Generators*)


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


(* ::Section:: *)
(*Cartan Matrix*)


(* ::Text:: *)
(*We define the Cartan matrix*)


(* ::Input::Initialization:: *)
cartanMatrix={{2,-1,0},{-1,2,-2},{0,-2,2}};


(* ::Section:: *)
(*Multi-Commutators*)


(* ::Text:: *)
(*Define the multi-commutator of f[i].*)
(*The function takes two or more arguments such that multiCom[-1,0,-1] = [ f[-1], [ f[0], f[-1] ]].*)


(* ::Text:: *)
(*The definition is recursive. *)
(*First we define the start*)


(* ::Input::Initialization:: *)
multiCom[ls__,-1]:=multiComRecursive[ls,f[-1]]
multiCom[ls__,0]:=multiComRecursive[ls,f[0]]
multiCom[ls__,1]:=multiComRecursive[ls,f[1]]


(* ::Text:: *)
(*then the recursion*)


(* ::Input::Initialization:: *)
multiComRecursive[ls__,last_]:=multiComRecursive[Apply[Sequence,Drop[{ls},-1]],com[f[Last[{ls}]],last]]


(* ::Text:: *)
(*and finally, the end*)


(* ::Input::Initialization:: *)
multiComRecursive[expr_]:=sortProd[expr//ExpandAll]
