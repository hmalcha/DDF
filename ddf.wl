(* ::Package:: *)

(* ::Title:: *)
(*DDF Package*)


(* ::Text:: *)
(*This is the DDF package. It facilitates a concrete realization of the Feingold-Frenkel algebra F, a rank 3 hyperbolic Kac-Moody algebra, in terms of a DDF construction.*)
(*The DDF package computes (tensor) DDF states and their commutators. Moreover, it introduces a number of operators that act on DDF states.*)
(*The most important operators are the affine generators, the Sugawara operator and the coset Virasoro operator.*)
(*Moreover the package also allows for the automatic calculation of the maximal tensor ground states of the Feingold-Frenkel algebra.*)


(* ::Text:: *)
(*The functions and operators defined in this package are derived from the papers [1, 2, 3] and appropriately adjusted to the Feingold-Frenkel algebra F .*)


(* ::Text:: *)
(*	[1] R.W. Gebert and H. Nicolai, On E(10) and the DDF construction, Commun. Math. Phys. 172 (1995), 571-622, arXiv:hep-th/9406175.*)


(* ::Text:: *)
(*	[2] R.W. Gebert and H. Nicolai, An Affine string vertex operator construction at arbitrary level, J. Math. Phys. 38 (1997), 4435-4450, arXiv:hep-th/9608014.*)


(* ::Text:: *)
(*	[3] S . Capolongo, A . Kleinschmidt, H . Malcha and H . Nicolai, "A string-like realization of hyperbolic Kac-Moody algebras", arXiv : 2411.18754 [hep-th] .*)


(* ::Text:: *)
(*The DDF Package is free software: you can redistribute it and/or modify it under the terms of the GNU General Public License as published by the Free Software Foundation, either version 3 of the License, or (at your option) any later version.*)
(*The DDF Package is distributed in the hope that it will be useful, but WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the GNU General Public License for more details.*)
(*You should have received a copy of the GNU General Public License along with the DDF Package. If not, see https://www.gnu.org/licenses/.*)


(* ::Text:: *)
(*Copyright \[Copyright] 2025*)
(*Hannes Malcha*)
(*hmalcha@ethz.ch*)


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
cartanMatrix::usage="The Catan matrix of the Feingold-Frenkel algebra F";


(* ::Subsection:: *)
(*Functions*)


(* ::Subsubsection:: *)
(*Fock States*)


(* ::Input::Initialization:: *)
prod::usage="\!\(\*
StyleBox[\"prod\",\nFontWeight->\"Bold\"]\)\!\(\*
StyleBox[\"[\",\nFontWeight->\"Bold\"]\)\!\(\*
StyleBox[\"{\",\nFontWeight->\"Bold\"]\)\!\(\*SubscriptBox[
StyleBox[\"u\",\nFontWeight->\"Bold\"], \(1\)]\)\!\(\*
StyleBox[\"[\",\nFontWeight->\"Bold\"]\)\!\(\*SubscriptBox[
StyleBox[\"m\",\nFontWeight->\"Bold\"], \(1\)]\)\!\(\*
StyleBox[\"]\",\nFontWeight->\"Bold\"]\)\!\(\*
StyleBox[\",\",\nFontWeight->\"Bold\"]\)\!\(\*
StyleBox[\" \",\nFontWeight->\"Bold\"]\)\!\(\*SubscriptBox[
StyleBox[\"u\",\nFontWeight->\"Bold\"], \(2\)]\)\!\(\*
StyleBox[\"[\",\nFontWeight->\"Bold\"]\)\!\(\*SubscriptBox[
StyleBox[\"m\",\nFontWeight->\"Bold\"], \(2\)]\)\!\(\*
StyleBox[\"]\",\nFontWeight->\"Bold\"]\)\!\(\*
StyleBox[\",\",\nFontWeight->\"Bold\"]\)\!\(\*
StyleBox[\" \",\nFontWeight->\"Bold\"]\)\!\(\*
StyleBox[\"...\",\nFontWeight->\"Bold\"]\)\!\(\*
StyleBox[\"}\",\nFontWeight->\"Bold\"]\)\!\(\*
StyleBox[\"]\",\nFontWeight->\"Bold\"]\) is a product of elements from the vector space of roots \!\(\*
StyleBox[SubscriptBox[\"u\", \"i\"],\nFontWeight->\"Bold\"]\)\!\(\*
StyleBox[\"[\",\nFontWeight->\"Bold\"]\)\!\(\*
StyleBox[SubscriptBox[\"m\", \"i\"],\nFontWeight->\"Bold\"]\)\!\(\*
StyleBox[\"]\",\nFontWeight->\"Bold\"]\)\!\(\*
StyleBox[\" \",\nFontWeight->\"Bold\"]\)\!\(\*
StyleBox[\"\[Element]\",\nFontWeight->\"Bold\"]\)\!\(\*
StyleBox[\" \",\nFontWeight->\"Bold\"]\)\!\(\*
StyleBox[SubscriptBox[\"\[CapitalLambda]\", \"\[DoubleStruckCapitalR]\"],\nFontWeight->\"Bold\"]\)\!\(\*
StyleBox[\" \",\nFontWeight->\"Bold\"]\)= \[DoubleStruckCapitalR] \[CircleTimes] \[CapitalLambda]. \!\(\*
StyleBox[SubscriptBox[\"u\", \"i\"],\nFontWeight->\"Bold\"]\)\!\(\*
StyleBox[\" \",\nFontWeight->\"Bold\"]\)\!\(\*
StyleBox[\"\[Element]\",\nFontWeight->\"Bold\"]\)\!\(\*
StyleBox[\" \",\nFontWeight->\"Bold\"]\)\!\(\*
StyleBox[\"span\",\nFontWeight->\"Bold\"]\)\!\(\*
StyleBox[\"{\",\nFontWeight->\"Bold\"]\)\!\(\*
StyleBox[\"r\",\nFontWeight->\"Bold\"]\)\!\(\*
StyleBox[\",\",\nFontWeight->\"Bold\"]\)\!\(\*
StyleBox[\"d\",\nFontWeight->\"Bold\"]\)\!\(\*
StyleBox[\",\",\nFontWeight->\"Bold\"]\)\!\(\*
StyleBox[\"s\",\nFontWeight->\"Bold\"]\)\!\(\*
StyleBox[\"}\",\nFontWeight->\"Bold\"]\) and \!\(\*
StyleBox[SubscriptBox[
StyleBox[\"m\",\nFontWeight->\"Bold\"], \"i\"],\nFontWeight->\"Bold\"]\)\!\(\*
StyleBox[\" \",\nFontWeight->\"Bold\"]\)\!\(\*
StyleBox[\"\[Element]\",\nFontWeight->\"Bold\"]\)\!\(\*
StyleBox[\" \",\nFontWeight->\"Bold\"]\)\!\(\*
StyleBox[\"\[CapitalNu]\",\nFontWeight->\"Bold\"]\). The product of creation operators, i.e. \!\(\*SubscriptBox[\(m\), \(i\)]\) < 0 for all i is commutative. The vector space of finite products of creation operators is denoted by S(\!\(\*SuperscriptBox[OverscriptBox[\(h\), \(^\)], \(i\)]\)).";


(* ::Input::Initialization:: *)
exp::usage="\!\(\*
StyleBox[\"exp\",\nFontWeight->\"Bold\"]\)\!\(\*
StyleBox[\"[\",\nFontWeight->\"Bold\"]\)\!\(\*
StyleBox[\"u\",\nFontWeight->\"Bold\"]\)\!\(\*
StyleBox[\"]\",\nFontWeight->\"Bold\"]\) defines the tachionic state corresponding to the root \!\(\*
StyleBox[\"u\",\nFontWeight->\"Bold\"]\)\!\(\*
StyleBox[\" \",\nFontWeight->\"Bold\"]\)\!\(\*
StyleBox[\"\[Element]\",\nFontWeight->\"Bold\"]\)\!\(\*
StyleBox[\" \",\nFontWeight->\"Bold\"]\)\!\(\*
StyleBox[\"span\",\nFontWeight->\"Bold\"]\)\!\(\*
StyleBox[\"{\",\nFontWeight->\"Bold\"]\)\!\(\*
StyleBox[\"r\",\nFontWeight->\"Bold\"]\)\!\(\*
StyleBox[\",\",\nFontWeight->\"Bold\"]\)\!\(\*
StyleBox[\"d\",\nFontWeight->\"Bold\"]\)\!\(\*
StyleBox[\",\",\nFontWeight->\"Bold\"]\)\!\(\*
StyleBox[\"s\",\nFontWeight->\"Bold\"]\)\!\(\*
StyleBox[\"}\",\nFontWeight->\"Bold\"]\). The state span the twisted group algebra \!\(\*TemplateBox[{},\n\"Reals\"]\){\[CapitalLambda]}. \!\(\*
StyleBox[\"exp\",\nFontWeight->\"Bold\"]\)\!\(\*
StyleBox[\"[\",\nFontWeight->\"Bold\"]\)\!\(\*
StyleBox[\"u\",\nFontWeight->\"Bold\"]\)\!\(\*
StyleBox[\"]\",\nFontWeight->\"Bold\"]\) appears in the second argument of \!\(\*
StyleBox[\"tp\",\nFontWeight->\"Bold\"]\) and \!\(\*
StyleBox[\"ddfProd\",\nFontWeight->\"Bold\"]\) or as the argument of \!\(\*
StyleBox[\"opA\",\nFontWeight->\"Bold\"]\) and \!\(\*
StyleBox[\"opB\",\nFontWeight->\"Bold\"]\).";


(* ::Input::Initialization:: *)
tp::usage="\!\(\*
StyleBox[\"tp\",\nFontWeight->\"Bold\"]\)\!\(\*
StyleBox[\"[\",\nFontWeight->\"Bold\"]\)\!\(\*
StyleBox[\"prod\",\nFontWeight->\"Bold\"]\)\!\(\*
StyleBox[\"[\",\nFontWeight->\"Bold\"]\)\!\(\*
StyleBox[\"{\",\nFontWeight->\"Bold\"]\)\!\(\*
StyleBox[\"...\",\nFontWeight->\"Bold\"]\)\!\(\*
StyleBox[\"}\",\nFontWeight->\"Bold\"]\)\!\(\*
StyleBox[\",\",\nFontWeight->\"Bold\"]\)\!\(\*
StyleBox[\" \",\nFontWeight->\"Bold\"]\)\!\(\*
StyleBox[\"exp\",\nFontWeight->\"Bold\"]\)\!\(\*
StyleBox[\"[\",\nFontWeight->\"Bold\"]\)\!\(\*
StyleBox[\"...\",\nFontWeight->\"Bold\"]\)\!\(\*
StyleBox[\"]\",\nFontWeight->\"Bold\"]\)\!\(\*
StyleBox[\"]\",\nFontWeight->\"Bold\"]\) is the tensor product of an element from the vector space of finite products of creation operators S(\!\(\*SuperscriptBox[OverscriptBox[\(h\), \(^\)], \(i\)]\)) and the twisted group algebra \!\(\*TemplateBox[{},\n\"Reals\"]\){\[CapitalLambda]}. \!\(\*
StyleBox[\"tp\",\nFontWeight->\"Bold\"]\) is an element of the Fock space \[ScriptCapitalF]. The functions \!\(\*
StyleBox[\"opA\",\nFontWeight->\"Bold\"]\), \!\(\*
StyleBox[\"opB\",\nFontWeight->\"Bold\"]\), \!\(\*
StyleBox[\"com\",\nFontWeight->\"Bold\"]\) and \!\(\*
StyleBox[\"toTp\",\nFontWeight->\"Bold\"]\) return a \!\(\*
StyleBox[\"tp\",\nFontWeight->\"Bold\"]\).";


(* ::Input::Initialization:: *)
sortProd::usage="\!\(\*
StyleBox[\"sortProd\",\nFontWeight->\"Bold\"]\)\!\(\*
StyleBox[\"[\",\nFontWeight->\"Bold\"]\)\!\(\*
StyleBox[\"\[Psi]\",\nFontWeight->\"Bold\"]\)\!\(\*
StyleBox[\"]\",\nFontWeight->\"Bold\"]\) normal orders the products of creation operator in a Fock state \!\(\*
StyleBox[\"\[Psi]\",\nFontWeight->\"Bold\"]\), i.e. a linear combination of tp[prod[{...}],exp[...]].";


(* ::Input::Initialization:: *)
virasoroOp::usage="\!\(\*
StyleBox[\"virasoroOp\",\nFontWeight->\"Bold\"]\)\!\(\*
StyleBox[\"[\",\nFontWeight->\"Bold\"]\)\!\(\*
StyleBox[\"m\",\nFontWeight->\"Bold\"]\)\!\(\*
StyleBox[\"]\",\nFontWeight->\"Bold\"]\)\!\(\*
StyleBox[\"[\",\nFontWeight->\"Bold\"]\)\!\(\*
StyleBox[\"\[Psi]\",\nFontWeight->\"Bold\"]\)\!\(\*
StyleBox[\"]\",\nFontWeight->\"Bold\"]\) computes the action of the Virasoro operator with mode number \!\(\*
StyleBox[\"m\",\nFontWeight->\"Bold\"]\) on a Fock state \!\(\*
StyleBox[\"\[Psi]\",\nFontWeight->\"Bold\"]\). A Fock state is called physical if it satisfies \!\(\*
StyleBox[\"(\",\nFontWeight->\"Bold\"]\)\!\(\*
StyleBox[\"virasoroOp\",\nFontWeight->\"Bold\"]\)\!\(\*
StyleBox[\"[\",\nFontWeight->\"Bold\"]\)\!\(\*
StyleBox[\"m\",\nFontWeight->\"Bold\"]\)\!\(\*
StyleBox[\"]\",\nFontWeight->\"Bold\"]\)\!\(\*
StyleBox[\"[\",\nFontWeight->\"Bold\"]\)\!\(\*
StyleBox[\"\[Psi]\",\nFontWeight->\"Bold\"]\)\!\(\*
StyleBox[\"]\",\nFontWeight->\"Bold\"]\)\!\(\*
StyleBox[\" \",\nFontWeight->\"Bold\"]\)\!\(\*
StyleBox[\"-\",\nFontWeight->\"Bold\"]\)\!\(\*
StyleBox[\" \",\nFontWeight->\"Bold\"]\)\!\(\*
StyleBox[\"KroneckerDelta\",\nFontWeight->\"Bold\"]\)\!\(\*
StyleBox[\"[\",\nFontWeight->\"Bold\"]\)\!\(\*
StyleBox[\"m\",\nFontWeight->\"Bold\"]\)\!\(\*
StyleBox[\",\",\nFontWeight->\"Bold\"]\)\!\(\*
StyleBox[\"0\",\nFontWeight->\"Bold\"]\)\!\(\*
StyleBox[\"]\",\nFontWeight->\"Bold\"]\)\!\(\*
StyleBox[\" \",\nFontWeight->\"Bold\"]\)\!\(\*
StyleBox[\"*\",\nFontWeight->\"Bold\"]\)\!\(\*
StyleBox[\" \",\nFontWeight->\"Bold\"]\)\!\(\*
StyleBox[\"\[Psi]\",\nFontWeight->\"Bold\"]\)\!\(\*
StyleBox[\")\",\nFontWeight->\"Bold\"]\)\!\(\*
StyleBox[\" \",\nFontWeight->\"Bold\"]\)\!\(\*
StyleBox[\"=\",\nFontWeight->\"Bold\"]\)\!\(\*
StyleBox[\" \",\nFontWeight->\"Bold\"]\)\!\(\*
StyleBox[\"0\",\nFontWeight->\"Bold\"]\) for all \!\(\*
StyleBox[\"m\",\nFontWeight->\"Bold\"]\)\!\(\*
StyleBox[\" \",\nFontWeight->\"Bold\"]\)\!\(\*
StyleBox[\"\[GreaterEqual]\",\nFontWeight->\"Bold\"]\)\!\(\*
StyleBox[\" \",\nFontWeight->\"Bold\"]\)\*
StyleBox[\(\!\(\*
StyleBox[\"0\",\nFontWeight->\"Bold\"]\) .\)]";


(* ::Subsubsection:: *)
(*DDF States*)


(* ::Input::Initialization:: *)
A::usage="\!\(\*
StyleBox[\"A\",\nFontWeight->\"Bold\"]\)\!\(\*
StyleBox[\"[\",\nFontWeight->\"Bold\"]\)\!\(\*
StyleBox[\"l\",\nFontWeight->\"Bold\"]\)\!\(\*
StyleBox[\",\",\nFontWeight->\"Bold\"]\)\!\(\*
StyleBox[\"m\",\nFontWeight->\"Bold\"]\)\!\(\*
StyleBox[\"]\",\nFontWeight->\"Bold\"]\) is the transversal DDF operator of level l and mode m. \!\(\*
StyleBox[\"A\",\nFontWeight->\"Bold\"]\)\!\(\*
StyleBox[\"[\",\nFontWeight->\"Bold\"]\)\!\(\*
StyleBox[\"l\",\nFontWeight->\"Bold\"]\)\!\(\*
StyleBox[\",\",\nFontWeight->\"Bold\"]\)\!\(\*
StyleBox[\"m\",\nFontWeight->\"Bold\"]\)\!\(\*
StyleBox[\"]\",\nFontWeight->\"Bold\"]\) is used in the first argument of \!\(\*
StyleBox[\"ddfProd\",\nFontWeight->\"Bold\"]\).";


(* ::Input::Initialization:: *)
B::usage="\!\(\*
StyleBox[\"B\",\nFontWeight->\"Bold\"]\)\!\(\*
StyleBox[\"[\",\nFontWeight->\"Bold\"]\)\!\(\*
StyleBox[\"l\",\nFontWeight->\"Bold\"]\)\!\(\*
StyleBox[\",\",\nFontWeight->\"Bold\"]\)\!\(\*
StyleBox[\"m\",\nFontWeight->\"Bold\"]\)\!\(\*
StyleBox[\"]\",\nFontWeight->\"Bold\"]\) is the longitudinal DDF operator of level l and mode m. \!\(\*
StyleBox[\"B\",\nFontWeight->\"Bold\"]\)\!\(\*
StyleBox[\"[\",\nFontWeight->\"Bold\"]\)\!\(\*
StyleBox[\"l\",\nFontWeight->\"Bold\"]\)\!\(\*
StyleBox[\",\",\nFontWeight->\"Bold\"]\)\!\(\*
StyleBox[\"m\",\nFontWeight->\"Bold\"]\)\!\(\*
StyleBox[\"]\",\nFontWeight->\"Bold\"]\) is used in the first argument of \!\(\*
StyleBox[\"ddfProd\",\nFontWeight->\"Bold\"]\).";


(* ::Input::Initialization:: *)
a::usage="\!\(\*
StyleBox[\"a\",\nFontWeight->\"Bold\"]\)\!\(\*
StyleBox[\"[\",\nFontWeight->\"Bold\"]\)\!\(\*
StyleBox[\"l\",\nFontWeight->\"Bold\"]\)\!\(\*
StyleBox[\",\",\nFontWeight->\"Bold\"]\)\!\(\*
StyleBox[\"n\",\nFontWeight->\"Bold\"]\)\!\(\*
StyleBox[\"]\",\nFontWeight->\"Bold\"]\)\!\(\*
StyleBox[\" \",\nFontWeight->\"Bold\"]\)\!\(\*
StyleBox[\"=\",\nFontWeight->\"Bold\"]\)\!\(\*
StyleBox[\" \",\nFontWeight->\"Bold\"]\)\!\(\*
StyleBox[\"-\",\nFontWeight->\"Bold\"]\)\!\(\*
StyleBox[\" \",\nFontWeight->\"Bold\"]\)\!\(\*
StyleBox[\"l\",\nFontWeight->\"Bold\"]\)\!\(\*
StyleBox[\" \",\nFontWeight->\"Bold\"]\)\!\(\*
StyleBox[\"*\",\nFontWeight->\"Bold\"]\)\!\(\*
StyleBox[\" \",\nFontWeight->\"Bold\"]\)\!\(\*
StyleBox[\"r\",\nFontWeight->\"Bold\"]\)\!\(\*
StyleBox[\" \",\nFontWeight->\"Bold\"]\)\!\(\*
StyleBox[\"-\",\nFontWeight->\"Bold\"]\)\!\(\*
StyleBox[\" \",\nFontWeight->\"Bold\"]\)\!\(\*
StyleBox[\"(\",\nFontWeight->\"Bold\"]\)\!\(\*
StyleBox[\"l\",\nFontWeight->\"Bold\"]\)\!\(\*
StyleBox[\" \",\nFontWeight->\"Bold\"]\)\!\(\*
StyleBox[\"+\",\nFontWeight->\"Bold\"]\)\!\(\*
StyleBox[\" \",\nFontWeight->\"Bold\"]\)\!\(\*
StyleBox[\"(\",\nFontWeight->\"Bold\"]\)\!\(\*
StyleBox[\"n\",\nFontWeight->\"Bold\"]\)\!\(\*
StyleBox[\"^\",\nFontWeight->\"Bold\"]\)\!\(\*
StyleBox[\"2\",\nFontWeight->\"Bold\"]\)\!\(\*
StyleBox[\" \",\nFontWeight->\"Bold\"]\)\!\(\*
StyleBox[\"-\",\nFontWeight->\"Bold\"]\)\!\(\*
StyleBox[\" \",\nFontWeight->\"Bold\"]\)\!\(\*
StyleBox[\"1\",\nFontWeight->\"Bold\"]\)\!\(\*
StyleBox[\")\",\nFontWeight->\"Bold\"]\)\!\(\*
StyleBox[\"/\",\nFontWeight->\"Bold\"]\)\!\(\*
StyleBox[\"l\",\nFontWeight->\"Bold\"]\)\!\(\*
StyleBox[\")\",\nFontWeight->\"Bold\"]\)\!\(\*
StyleBox[\" \",\nFontWeight->\"Bold\"]\)\!\(\*
StyleBox[\"d\",\nFontWeight->\"Bold\"]\)\!\(\*
StyleBox[\" \",\nFontWeight->\"Bold\"]\)\!\(\*
StyleBox[\"+\",\nFontWeight->\"Bold\"]\)\!\(\*
StyleBox[\" \",\nFontWeight->\"Bold\"]\)\!\(\*
StyleBox[\"n\",\nFontWeight->\"Bold\"]\)\!\(\*
StyleBox[\" \",\nFontWeight->\"Bold\"]\)\!\(\*
StyleBox[\"*\",\nFontWeight->\"Bold\"]\)\!\(\*
StyleBox[\" \",\nFontWeight->\"Bold\"]\)\!\(\*
StyleBox[\"s\",\nFontWeight->\"Bold\"]\) is the tachionyc momentum of a DDF state of level l and weight n.";


(* ::Input::Initialization:: *)
ddfProd::usage="\!\(\*
StyleBox[\"ddfProd\",\nFontWeight->\"Bold\"]\)\!\(\*
StyleBox[\"[\",\nFontWeight->\"Bold\"]\)\!\(\*
StyleBox[\"{\",\nFontWeight->\"Bold\"]\)\!\(\*
StyleBox[\"...\",\nFontWeight->\"Bold\"]\)\!\(\*
StyleBox[\"}\",\nFontWeight->\"Bold\"]\)\!\(\*
StyleBox[\",\",\nFontWeight->\"Bold\"]\)\!\(\*
StyleBox[\" \",\nFontWeight->\"Bold\"]\)\!\(\*
StyleBox[\"exp\",\nFontWeight->\"Bold\"]\)\!\(\*
StyleBox[\"[\",\nFontWeight->\"Bold\"]\)\!\(\*
StyleBox[\"a\",\nFontWeight->\"Bold\"]\)\!\(\*
StyleBox[\"[\",\nFontWeight->\"Bold\"]\)\!\(\*
StyleBox[\"l\",\nFontWeight->\"Bold\"]\)\!\(\*
StyleBox[\",\",\nFontWeight->\"Bold\"]\)\!\(\*
StyleBox[\" \",\nFontWeight->\"Bold\"]\)\!\(\*
StyleBox[\"n\",\nFontWeight->\"Bold\"]\)\!\(\*
StyleBox[\"]\",\nFontWeight->\"Bold\"]\)\!\(\*
StyleBox[\"]\",\nFontWeight->\"Bold\"]\) defines a product of DDF operators acting on a tachyonic state. The first argument is a list of transversal and longitudinal DDF operators \!\(\*
StyleBox[\"A\",\nFontWeight->\"Bold\"]\)\!\(\*
StyleBox[\"[\",\nFontWeight->\"Bold\"]\)\!\(\*
StyleBox[\"l\",\nFontWeight->\"Bold\"]\)\!\(\*
StyleBox[\",\",\nFontWeight->\"Bold\"]\)\!\(\*
StyleBox[\"m\",\nFontWeight->\"Bold\"]\)\!\(\*
StyleBox[\"]\",\nFontWeight->\"Bold\"]\) and \!\(\*
StyleBox[\"B\",\nFontWeight->\"Bold\"]\)\!\(\*
StyleBox[\"[\",\nFontWeight->\"Bold\"]\)\!\(\*
StyleBox[\"l\",\nFontWeight->\"Bold\"]\)\!\(\*
StyleBox[\",\",\nFontWeight->\"Bold\"]\)\!\(\*
StyleBox[\"m\",\nFontWeight->\"Bold\"]\)\!\(\*
StyleBox[\"]\",\nFontWeight->\"Bold\"]\). The second argument is a tachyonic state \!\(\*
StyleBox[\"exp\",\nFontWeight->\"Bold\"]\)\!\(\*
StyleBox[\"[\",\nFontWeight->\"Bold\"]\)\!\(\*
StyleBox[\"a\",\nFontWeight->\"Bold\"]\)\!\(\*
StyleBox[\"[\",\nFontWeight->\"Bold\"]\)\!\(\*
StyleBox[\"l\",\nFontWeight->\"Bold\"]\)\!\(\*
StyleBox[\",\",\nFontWeight->\"Bold\"]\)\!\(\*
StyleBox[\" \",\nFontWeight->\"Bold\"]\)\!\(\*
StyleBox[\"n\",\nFontWeight->\"Bold\"]\)\!\(\*
StyleBox[\"]\",\nFontWeight->\"Bold\"]\)\!\(\*
StyleBox[\"]\",\nFontWeight->\"Bold\"]\)\!\(\*
StyleBox[\" \",\nFontWeight->\"Bold\"]\)with momentum \!\(\*
StyleBox[\"a\",\nFontWeight->\"Bold\"]\)\!\(\*
StyleBox[\"[\",\nFontWeight->\"Bold\"]\)\!\(\*
StyleBox[\"l\",\nFontWeight->\"Bold\"]\)\!\(\*
StyleBox[\",\",\nFontWeight->\"Bold\"]\)\!\(\*
StyleBox[\" \",\nFontWeight->\"Bold\"]\)\!\(\*
StyleBox[\"n\",\nFontWeight->\"Bold\"]\)\!\(\*
StyleBox[\"]\",\nFontWeight->\"Bold\"]\). If the list of DDF operators is not normal ordered or contains annihilation operators \!\(\*
StyleBox[\"ddfProd\",\nFontWeight->\"Bold\"]\) will order the product and act with the annihilation operators respecting the commutation relations of DDF operators.";


(* ::Input::Initialization:: *)
ddfTp::usage="\!\(\*
StyleBox[\"ddfTp\",\nFontWeight->\"Bold\"]\)\!\(\*
StyleBox[\"[\",\nFontWeight->\"Bold\"]\)\!\(\*
StyleBox[SubscriptBox[\"\[Phi]\", \"1\"],\nFontWeight->\"Bold\"]\)\!\(\*
StyleBox[\",\",\nFontWeight->\"Bold\"]\)\!\(\*
StyleBox[\" \",\nFontWeight->\"Bold\"]\)\!\(\*
StyleBox[SubscriptBox[\"\[Phi]\", \"2\"],\nFontWeight->\"Bold\"]\)] is the tensor product of two DDF states \!\(\*SubscriptBox[\(\[Phi]\), \(1\)]\) and \!\(\*SubscriptBox[\(\[Phi]\), \(2\)]\). The coset Virasoro operators act on the vector space of tensor products of DDF states. \!\(\*
StyleBox[\"ddfTp\",\nFontWeight->\"Bold\"]\)\*
StyleBox[\(\!\(\*
StyleBox[\" \",\nFontWeight->\"Bold\"]\) \)]can be nested to generate a multiple tensor product.";


(* ::Input::Initialization:: *)
autoCom::usage="\!\(\*
StyleBox[\"autoCom\",\nFontWeight->\"Bold\"]\)\!\(\*
StyleBox[\"[\",\nFontWeight->\"Bold\"]\)\!\(\*
StyleBox[\"\[Psi]\",\nFontWeight->\"Bold\"]\)] takes a DDF tensor product \!\(\*
StyleBox[\"ddfTp\",\nFontWeight->\"Bold\"]\)\!\(\*
StyleBox[\"[\",\nFontWeight->\"Bold\"]\)\!\(\*
StyleBox[\"...\",\nFontWeight->\"Bold\"]\)\!\(\*
StyleBox[\"]\",\nFontWeight->\"Bold\"]\) replaces all occurences of \!\(\*
StyleBox[\"ddfTp\",\nFontWeight->\"Bold\"]\) with \!\(\*
StyleBox[\"com\",\nFontWeight->\"Bold\"]\), simplifies the result and returns a \!\(\*
StyleBox[\"ddfProd\",\nFontWeight->\"Bold\"]\).";


(* ::Subsubsection:: *)
(*Vertex Operator Algebra*)


(* ::Input::Initialization:: *)
sp::usage="\!\(\*
StyleBox[\"sp\",\nFontWeight->\"Bold\"]\)\!\(\*
StyleBox[\"[\",\nFontWeight->\"Bold\"]\)\!\(\*SubscriptBox[
StyleBox[\"u\",\nFontWeight->\"Bold\"], \(1\)]\)\!\(\*
StyleBox[\",\",\nFontWeight->\"Bold\"]\)\!\(\*
StyleBox[\" \",\nFontWeight->\"Bold\"]\)\!\(\*SubscriptBox[
StyleBox[\"u\",\nFontWeight->\"Bold\"], \(2\)]\)\!\(\*
StyleBox[\"]\",\nFontWeight->\"Bold\"]\) computes the scalar product of two roots \!\(\*
StyleBox[SubscriptBox[\"u\", \"1\"],\nFontWeight->\"Bold\"]\)\!\(\*
StyleBox[\",\",\nFontWeight->\"Bold\"]\)\!\(\*
StyleBox[\" \",\nFontWeight->\"Bold\"]\)\!\(\*
StyleBox[SubscriptBox[
StyleBox[\"u\",\nFontWeight->\"Bold\"], \"2\"],\nFontWeight->\"Bold\"]\)\!\(\*
StyleBox[\" \",\nFontWeight->\"Bold\"]\)\!\(\*
StyleBox[\"\[Element]\",\nFontWeight->\"Bold\"]\)\!\(\*
StyleBox[\" \",\nFontWeight->\"Bold\"]\)\!\(\*
StyleBox[\"span\",\nFontWeight->\"Bold\"]\)\!\(\*
StyleBox[\"{\",\nFontWeight->\"Bold\"]\)\!\(\*
StyleBox[\"r\",\nFontWeight->\"Bold\"]\)\!\(\*
StyleBox[\",\",\nFontWeight->\"Bold\"]\)\!\(\*
StyleBox[\"d\",\nFontWeight->\"Bold\"]\)\!\(\*
StyleBox[\",\",\nFontWeight->\"Bold\"]\)\!\(\*
StyleBox[\"s\",\nFontWeight->\"Bold\"]\)\!\(\*
StyleBox[\"}\",\nFontWeight->\"Bold\"]\) according to the Cartan matrix. Expects two arguments which are linear combinations of roots. Returns a \!\(\*TemplateBox[{},\n\"Complexes\"]\) number.";


(* ::Input::Initialization:: *)
com::usage="\!\(\*
StyleBox[\"com\",\nFontWeight->\"Bold\"]\)\!\(\*
StyleBox[\"[\",\nFontWeight->\"Bold\"]\)\!\(\*SubscriptBox[
StyleBox[\"\[Psi]\",\nFontWeight->\"Bold\"], \(1\)]\)\!\(\*
StyleBox[\",\",\nFontWeight->\"Bold\"]\)\!\(\*
StyleBox[\" \",\nFontWeight->\"Bold\"]\)\!\(\*SubscriptBox[\(\[Psi]\), \(2\)]\)] computes the commutator of two fock states \!\(\*SubscriptBox[\(\[Psi]\), \(1\)]\), \!\(\*SubscriptBox[\(\[Psi]\), \(2\)]\) \[Element] \[ScriptCapitalF]. Takes linear combinations of \!\(\*
StyleBox[\"ddfProd\",\nFontWeight->\"Bold\"]\) or \!\(\*
StyleBox[\"tp\",\nFontWeight->\"Bold\"]\) as arguments. Returns a Fock state.";


(* ::Subsubsection:: *)
(*DDF Vertex Operators*)


(* ::Input::Initialization:: *)
opA::usage="\!\(\*
StyleBox[\"opA\",\nFontWeight->\"Bold\"]\)\!\(\*
StyleBox[\"[\",\nFontWeight->\"Bold\"]\)\!\(\*
StyleBox[\"l\",\nFontWeight->\"Bold\"]\)\!\(\*
StyleBox[\",\",\nFontWeight->\"Bold\"]\)\!\(\*
StyleBox[\"m\",\nFontWeight->\"Bold\"]\)\!\(\*
StyleBox[\"]\",\nFontWeight->\"Bold\"]\)\!\(\*
StyleBox[\"[\",\nFontWeight->\"Bold\"]\)\!\(\*
StyleBox[\"state\",\nFontWeight->\"Bold\"]\)\!\(\*
StyleBox[\"]\",\nFontWeight->\"Bold\"]\) is the transversal DDF operator of level l and mode m. It acts on other DDF operators \!\(\*
StyleBox[\"opA\",\nFontWeight->\"Bold\"]\) or \!\(\*
StyleBox[\"opB\",\nFontWeight->\"Bold\"]\) or tachionic states \!\(\*
StyleBox[\"exp\",\nFontWeight->\"Bold\"]\)\!\(\*
StyleBox[\"[\",\nFontWeight->\"Bold\"]\)\!\(\*
StyleBox[\"a\",\nFontWeight->\"Bold\"]\)\!\(\*
StyleBox[\"[\",\nFontWeight->\"Bold\"]\)\!\(\*
StyleBox[\"l\",\nFontWeight->\"Bold\"]\)\!\(\*
StyleBox[\",\",\nFontWeight->\"Bold\"]\)\!\(\*
StyleBox[\"m\",\nFontWeight->\"Bold\"]\)\!\(\*
StyleBox[\"]\",\nFontWeight->\"Bold\"]\)\!\(\*
StyleBox[\"]\",\nFontWeight->\"Bold\"]\). Returns the resulting state as a Fock state (see also \!\(\*
StyleBox[\"tp\",\nFontWeight->\"Bold\"]\)).";


(* ::Input::Initialization:: *)
opB::usage="\!\(\*
StyleBox[\"opB\",\nFontWeight->\"Bold\"]\)\!\(\*
StyleBox[\"[\",\nFontWeight->\"Bold\"]\)\!\(\*
StyleBox[\"l\",\nFontWeight->\"Bold\"]\)\!\(\*
StyleBox[\",\",\nFontWeight->\"Bold\"]\)\!\(\*
StyleBox[\"m\",\nFontWeight->\"Bold\"]\)\!\(\*
StyleBox[\"]\",\nFontWeight->\"Bold\"]\)\!\(\*
StyleBox[\"[\",\nFontWeight->\"Bold\"]\)\!\(\*
StyleBox[\"state\",\nFontWeight->\"Bold\"]\)\!\(\*
StyleBox[\"]\",\nFontWeight->\"Bold\"]\) is the longitudinal DDF operator of level l and mode m. It acts on other DDF operators \!\(\*
StyleBox[\"opA\",\nFontWeight->\"Bold\"]\) or \!\(\*
StyleBox[\"opB\",\nFontWeight->\"Bold\"]\) or tachionic states \!\(\*
StyleBox[\"exp\",\nFontWeight->\"Bold\"]\)\!\(\*
StyleBox[\"[\",\nFontWeight->\"Bold\"]\)\!\(\*
StyleBox[\"a\",\nFontWeight->\"Bold\"]\)\!\(\*
StyleBox[\"[\",\nFontWeight->\"Bold\"]\)\!\(\*
StyleBox[\"l\",\nFontWeight->\"Bold\"]\)\!\(\*
StyleBox[\",\",\nFontWeight->\"Bold\"]\)\!\(\*
StyleBox[\"m\",\nFontWeight->\"Bold\"]\)\!\(\*
StyleBox[\"]\",\nFontWeight->\"Bold\"]\)\!\(\*
StyleBox[\"]\",\nFontWeight->\"Bold\"]\). Returns the resulting state as a Fock state (see also \!\(\*
StyleBox[\"tp\",\nFontWeight->\"Bold\"]\)).";


(* ::Input::Initialization:: *)
toTp::usage="\!\(\*
StyleBox[\"toTp\",\nFontWeight->\"Bold\"]\)\!\(\*
StyleBox[\"[\",\nFontWeight->\"Bold\"]\)\!\(\*
StyleBox[\"\[Phi]\",\nFontWeight->\"Bold\"]\)\!\(\*
StyleBox[\"]\",\nFontWeight->\"Bold\"]\) finds the Fock state representation corresponding to the DDF state \!\(\*
StyleBox[\"\[Phi]\",\nFontWeight->\"Bold\"]\). If possible \!\(\*
StyleBox[\"toTp\",\nFontWeight->\"Bold\"]\) will utilize the database of Fock state representations of DDF states to quickly deliver a result. If the required states are not available in the database a warning message is issued an the calculation is performed manually. This generally can take while. Especially, when longitudinal DDF operators are involved.";


(* ::Input::Initialization:: *)
toDDF::usage="\!\(\*
StyleBox[\"toDDF\",\nFontWeight->\"Bold\"]\)\!\(\*
StyleBox[\"[\",\nFontWeight->\"Bold\"]\)\!\(\*
StyleBox[\"\[Psi]\",\nFontWeight->\"Bold\"]\)\!\(\*
StyleBox[\"]\",\nFontWeight->\"Bold\"]\) turns a Fock state \!\(\*
StyleBox[\"\[Psi]\",\nFontWeight->\"Bold\"]\) into a DDF state. Works only if a basis of DDF states with the correct level, depth and weight corresponding to the Fock state exist in the database. Otherwise the unevaluated expression is returned together with an error message. If \!\(\*
StyleBox[\"\[Psi]\",\nFontWeight->\"Bold\"]\) is not an element of the DDF algebra, a warning message is issuded and the unevaluated expression is returned";


(* ::Subsubsection:: *)
(*Operator Actions*)


(* ::Input::Initialization:: *)
rank::usage="\!\(\*
StyleBox[\"rank\",\nFontWeight->\"Bold\"]\)\!\(\*
StyleBox[\"[\",\nFontWeight->\"Bold\"]\)\!\(\*
StyleBox[\"list\",\nFontWeight->\"Bold\"]\)\!\(\*
StyleBox[\"]\",\nFontWeight->\"Bold\"]\) returns the rank, i.e the number of linearly independent elements, of a list of \!\(\*
StyleBox[\"tp\",\nFontWeight->\"Bold\"]\)\!\(\*
StyleBox[\"[\",\nFontWeight->\"Bold\"]\)\!\(\*
StyleBox[\"...\",\nFontWeight->\"Bold\"]\)\!\(\*
StyleBox[\"]\",\nFontWeight->\"Bold\"]\)\!\(\*
StyleBox[\",\",\nFontWeight->\"Bold\"]\) \!\(\*
StyleBox[\"ddfProd\",\nFontWeight->\"Bold\"]\)\!\(\*
StyleBox[\"[\",\nFontWeight->\"Bold\"]\)\!\(\*
StyleBox[\"...\",\nFontWeight->\"Bold\"]\)\!\(\*
StyleBox[\"]\",\nFontWeight->\"Bold\"]\) or \!\(\*
StyleBox[\"ddfTp\",\nFontWeight->\"Bold\"]\)\!\(\*
StyleBox[\"[\",\nFontWeight->\"Bold\"]\)\!\(\*
StyleBox[\"...\",\nFontWeight->\"Bold\"]\)\!\(\*
StyleBox[\"]\",\nFontWeight->\"Bold\"]\).";


(* ::Input::Initialization:: *)
linearIndependenQ::usage="\!\(\*
StyleBox[\"linearIndependenQ\",\nFontWeight->\"Bold\"]\)\!\(\*
StyleBox[\"[\",\nFontWeight->\"Bold\"]\)\!\(\*
StyleBox[\"list\",\nFontWeight->\"Bold\"]\)\!\(\*
StyleBox[\"]\",\nFontWeight->\"Bold\"]\) return true of the element in a list of \!\(\*
StyleBox[\"tp\",\nFontWeight->\"Bold\"]\)\!\(\*
StyleBox[\"[\",\nFontWeight->\"Bold\"]\)\!\(\*
StyleBox[\"...\",\nFontWeight->\"Bold\"]\)\!\(\*
StyleBox[\"]\",\nFontWeight->\"Bold\"]\)\!\(\*
StyleBox[\",\",\nFontWeight->\"Bold\"]\) \!\(\*
StyleBox[\"ddfProd\",\nFontWeight->\"Bold\"]\)\!\(\*
StyleBox[\"[\",\nFontWeight->\"Bold\"]\)\!\(\*
StyleBox[\"...\",\nFontWeight->\"Bold\"]\)\!\(\*
StyleBox[\"]\",\nFontWeight->\"Bold\"]\) or \!\(\*
StyleBox[\"ddfTp\",\nFontWeight->\"Bold\"]\)\!\(\*
StyleBox[\"[\",\nFontWeight->\"Bold\"]\)\!\(\*
StyleBox[\"...\",\nFontWeight->\"Bold\"]\)\!\(\*
StyleBox[\"]\",\nFontWeight->\"Bold\"]\) are linearly independent.";


(* ::Input::Initialization:: *)
affineE::usage="\!\(\*
StyleBox[\"affineE\",\nFontWeight->\"Bold\"]\)\!\(\*
StyleBox[\"[\",\nFontWeight->\"Bold\"]\)\!\(\*
StyleBox[\"m\",\nFontWeight->\"Bold\"]\)\!\(\*
StyleBox[\"]\",\nFontWeight->\"Bold\"]\)\!\(\*
StyleBox[\"[\",\nFontWeight->\"Bold\"]\)\!\(\*
StyleBox[\"state\",\nFontWeight->\"Bold\"]\)\!\(\*
StyleBox[\"]\",\nFontWeight->\"Bold\"]\) computes the action of the affine generator\!\(\*SuperscriptBox[\(\\\ \), \([l]\)]\)\!\(\*SubscriptBox[\(E\), \(m\)]\) on a Fock state or a DDF state. The level l is obtained automatically from the state." ;


(* ::Input::Initialization:: *)
affineF::usage="\!\(\*
StyleBox[\"affineF\",\nFontWeight->\"Bold\"]\)\!\(\*
StyleBox[\"[\",\nFontWeight->\"Bold\"]\)\!\(\*
StyleBox[\"m\",\nFontWeight->\"Bold\"]\)\!\(\*
StyleBox[\"]\",\nFontWeight->\"Bold\"]\)\!\(\*
StyleBox[\"[\",\nFontWeight->\"Bold\"]\)\!\(\*
StyleBox[\"state\",\nFontWeight->\"Bold\"]\)\!\(\*
StyleBox[\"]\",\nFontWeight->\"Bold\"]\) computes the action of the affine generator\!\(\*SuperscriptBox[\(\\\ \), \([l]\)]\)\!\(\*SubscriptBox[\(F\), \(m\)]\) on a Fock state or a DDF state. The level l is obtained automatically from the state." ;


(* ::Input::Initialization:: *)
affineH::usage="\!\(\*
StyleBox[\"affineH\",\nFontWeight->\"Bold\"]\)\!\(\*
StyleBox[\"[\",\nFontWeight->\"Bold\"]\)\!\(\*
StyleBox[\"m\",\nFontWeight->\"Bold\"]\)\!\(\*
StyleBox[\"]\",\nFontWeight->\"Bold\"]\)\!\(\*
StyleBox[\"[\",\nFontWeight->\"Bold\"]\)\!\(\*
StyleBox[\"state\",\nFontWeight->\"Bold\"]\)\!\(\*
StyleBox[\"]\",\nFontWeight->\"Bold\"]\) computes the action of the affine generator\!\(\*SuperscriptBox[\(\\\ \), \([l]\)]\)\!\(\*SubscriptBox[\(H\), \(m\)]\) on a Fock state or a DDF state. The level l is obtained automatically from the state." ;


(* ::Input::Initialization:: *)
sugawaraOp::usage="\!\(\*
StyleBox[\"sugwaraOp\",\nFontWeight->\"Bold\"]\)\!\(\*
StyleBox[\"[\",\nFontWeight->\"Bold\"]\)\!\(\*
StyleBox[\"m\",\nFontWeight->\"Bold\"]\)\!\(\*
StyleBox[\"]\",\nFontWeight->\"Bold\"]\)\!\(\*
StyleBox[\"[\",\nFontWeight->\"Bold\"]\)\!\(\*
StyleBox[\"\[Phi]\",\nFontWeight->\"Bold\"]\)\!\(\*
StyleBox[\"]\",\nFontWeight->\"Bold\"]\) computes the action of the Sugawara operator\!\(\*SuperscriptBox[\(\\\ \), \([l]\)]\)\!\(\*SubscriptBox[SuperscriptBox[\(L\), \(sug\)], \(m\)]\) on a DDF state \[Phi]. The level l is obtained automatically from the state. The operator can also be applied to (nested) tensor product of DDF states.";


(* ::Input::Initialization:: *)
cosetVirasoroOp::usage="\!\(\*
StyleBox[\"cosetVirasoroOp\",\nFontWeight->\"Bold\"]\)\!\(\*
StyleBox[\"[\",\nFontWeight->\"Bold\"]\)m\!\(\*
StyleBox[\"]\",\nFontWeight->\"Bold\"]\)\!\(\*
StyleBox[\"[\",\nFontWeight->\"Bold\"]\)\[Phi]] computes the action of the coset Virasoro operator\!\(\*SuperscriptBox[\(\\\ \), \([l]\)]\)\!\(\*SubscriptBox[SuperscriptBox[\(L\), \(coset\)], \(m\)]\) on a DDF state \[Phi]. The level l is obtained automatically from the state. he operator can also be applied to (nested) tensor product of DDF states. \!\(\*
StyleBox[\"cosetVirasoroOp\",\nFontWeight->\"Bold\"]\)\!\(\*
StyleBox[\"[\",\nFontWeight->\"Bold\"]\)\!\(\*
StyleBox[\"l\",\nFontWeight->\"Bold\"]\)\!\(\*
StyleBox[\",\",\nFontWeight->\"Bold\"]\)\!\(\*
StyleBox[\" \",\nFontWeight->\"Bold\"]\)m\!\(\*
StyleBox[\"]\",\nFontWeight->\"Bold\"]\)\!\(\*
StyleBox[\"[\",\nFontWeight->\"Bold\"]\)\[Phi]] computes the action of the level l coset Virasoro operator\!\(\*SuperscriptBox[\(\\\ \), \([l]\)]\)\!\(\*SubscriptBox[SuperscriptBox[\(L\), \(coset\)], \(m\)]\) on a nested DDF state of total level \[GreaterEqual] l. In this case the operator is inserted (automatically) at the appropriate position.";


(* ::Subsubsection:: *)
(*Ground State Computer*)


(* ::Input::Initialization:: *)
findTensorStates::usage= "\!\(\*
StyleBox[\"findTensorStates\",\nFontWeight->\"Bold\"]\)\!\(\*
StyleBox[\"[\",\nFontWeight->\"Bold\"]\)\!\(\*
StyleBox[\"l\",\nFontWeight->\"Bold\"]\)\!\(\*
StyleBox[\",\",\nFontWeight->\"Bold\"]\)\!\(\*
StyleBox[\" \",\nFontWeight->\"Bold\"]\)\!\(\*
StyleBox[\"d\",\nFontWeight->\"Bold\"]\)\!\(\*
StyleBox[\",\",\nFontWeight->\"Bold\"]\)\!\(\*
StyleBox[\" \",\nFontWeight->\"Bold\"]\)\!\(\*
StyleBox[\"w\",\nFontWeight->\"Bold\"]\)\!\(\*
StyleBox[\"]\",\nFontWeight->\"Bold\"]\) returns a list of all DDF tensor state with the given total level \!\(\*
StyleBox[\"l\",\nFontWeight->\"Bold\"]\), toal depth \!\(\*
StyleBox[\"d\",\nFontWeight->\"Bold\"]\) and total weight \!\(\*
StyleBox[\"w\",\nFontWeight->\"Bold\"]\)."


(* ::Input::Initialization:: *)
findTensorGroundState::usage= "\!\(\*
StyleBox[\"findTensorGroundState\",\nFontWeight->\"Bold\"]\)\!\(\*
StyleBox[\"[\",\nFontWeight->\"Bold\"]\)\!\(\*
StyleBox[\"{\",\nFontWeight->\"Bold\"]\)\!\(\*
StyleBox[\"eigenvalues\",\nFontWeight->\"Bold\"]\)\!\(\*
StyleBox[\"}\",\nFontWeight->\"Bold\"]\)\!\(\*
StyleBox[\",\",\nFontWeight->\"Bold\"]\)\!\(\*
StyleBox[\" \",\nFontWeight->\"Plain\"]\)\!\(\*
StyleBox[\"{\",\nFontWeight->\"Bold\"]\)\!\(\*
StyleBox[\"-\",\nFontWeight->\"Bold\"]\)\!\(\*
StyleBox[SubscriptBox[\"r\", 
RowBox[{\"-\", \"1\"}]],\nFontWeight->\"Bold\"]\)\!\(\*
StyleBox[\",\",\nFontWeight->\"Bold\"]\)\!\(\*
StyleBox[\" \",\nFontWeight->\"Bold\"]\)\!\(\*
StyleBox[\"-\",\nFontWeight->\"Bold\"]\)\!\(\*
StyleBox[SubscriptBox[\"r\", \"0\"],\nFontWeight->\"Bold\"]\)\!\(\*
StyleBox[\",\",\nFontWeight->\"Bold\"]\)\!\(\*
StyleBox[\" \",\nFontWeight->\"Bold\"]\)\!\(\*
StyleBox[\"-\",\nFontWeight->\"Bold\"]\)\!\(\*
StyleBox[SubscriptBox[\"r\", \"1\"],\nFontWeight->\"Bold\"]\)\!\(\*
StyleBox[\"}\",\nFontWeight->\"Bold\"]\)\!\(\*
StyleBox[\"]\",\nFontWeight->\"Bold\"]\) returns the DDF tensor ground with dominant root \!\(\*
StyleBox[\"{\",\nFontWeight->\"Bold\"]\)\!\(\*
StyleBox[\"-\",\nFontWeight->\"Bold\"]\)\!\(\*
StyleBox[SubscriptBox[\"r\", 
RowBox[{\"-\", \"1\"}]],\nFontWeight->\"Bold\"]\)\!\(\*
StyleBox[\",\",\nFontWeight->\"Bold\"]\)\!\(\*
StyleBox[\" \",\nFontWeight->\"Bold\"]\)\!\(\*
StyleBox[\"-\",\nFontWeight->\"Bold\"]\)\!\(\*
StyleBox[SubscriptBox[\"r\", \"0\"],\nFontWeight->\"Bold\"]\)\!\(\*
StyleBox[\",\",\nFontWeight->\"Bold\"]\)\!\(\*
StyleBox[\" \",\nFontWeight->\"Bold\"]\)\!\(\*
StyleBox[\"-\",\nFontWeight->\"Bold\"]\)\!\(\*
StyleBox[SubscriptBox[\"r\", \"1\"],\nFontWeight->\"Bold\"]\)\!\(\*
StyleBox[\"}\",\nFontWeight->\"Bold\"]\)\!\(\*
StyleBox[\" \",\nFontWeight->\"Bold\"]\)and coset Virasoro eigenvalues \!\(\*
StyleBox[\"{\",\nFontWeight->\"Bold\"]\)\!\(\*
StyleBox[\"eigenvalues\",\nFontWeight->\"Bold\"]\)\!\(\*
StyleBox[\"}\",\nFontWeight->\"Bold\"]\). The root must be the dominant root, i.e. largest \!\(\*
StyleBox[\"-\",\nFontWeight->\"Bold\"]\)\!\(\*
StyleBox[SubscriptBox[\"r\", \"1\"],\nFontWeight->\"Bold\"]\)\*
StyleBox[\(\!\(\*
StyleBox[\" \",\nFontWeight->\"Bold\"]\) \)]of the associated multiplet. The list of eigenvalues is descending in the level."


(* ::Subsubsection:: *)
(*Multi-Commutators*)


(* ::Input::Initialization:: *)
e::usage="\!\(\*
StyleBox[\"e\",\nFontWeight->\"Bold\"]\)\!\(\*
StyleBox[\"[\",\nFontWeight->\"Bold\"]\)\!\(\*
StyleBox[\"i\",\nFontWeight->\"Bold\"]\)\!\(\*
StyleBox[\"]\",\nFontWeight->\"Bold\"]\) is the Chevalley-Serre generator \!\(\*SubscriptBox[\(e\), \(i\)]\) with i \[Element] {-1,0,1}.";


(* ::Input::Initialization:: *)
f::usage="\!\(\*
StyleBox[\"f\",\nFontWeight->\"Bold\"]\)\!\(\*
StyleBox[\"[\",\nFontWeight->\"Bold\"]\)\!\(\*
StyleBox[\"i\",\nFontWeight->\"Bold\"]\)\!\(\*
StyleBox[\"]\",\nFontWeight->\"Bold\"]\) is the Chevalley-Serre generator \!\(\*SubscriptBox[\(f\), \(i\)]\) with i \[Element] {-1,0,1}.";


(* ::Input::Initialization:: *)
h::usage="\!\(\*
StyleBox[\"h\",\nFontWeight->\"Bold\"]\)\!\(\*
StyleBox[\"[\",\nFontWeight->\"Bold\"]\)\!\(\*
StyleBox[\"i\",\nFontWeight->\"Bold\"]\)\!\(\*
StyleBox[\"]\",\nFontWeight->\"Bold\"]\) is the Chevalley-Serre generator \!\(\*SubscriptBox[\(h\), \(i\)]\) with i \[Element] {-1,0,1}.";


(* ::Input::Initialization:: *)
multiCom::usage="\!\(\*
StyleBox[\"multiCom\",\nFontWeight->\"Bold\"]\)\!\(\*
StyleBox[\"[\",\nFontWeight->\"Bold\"]\)\!\(\*SubscriptBox[
StyleBox[\"i\",\nFontWeight->\"Bold\"], \(1\)]\), \!\(\*SubscriptBox[\(i\), \(2\)]\), ...\!\(\*
StyleBox[\"]\",\nFontWeight->\"Bold\"]\) computes the multicommutator [\!\(\*SubscriptBox[\(f\), SubscriptBox[\(i\), \(1\)]]\), [\!\(\*SubscriptBox[\(f\), SubscriptBox[\(i\), \(2\)]]\), [ ... ] .. ]], where indices are from the set -1, 0, 1. Returns a Fock state.";


(* ::Section:: *)
(*Begin Private*)


(* ::Input::Initialization:: *)
Begin["`Private`"]


(* ::Section:: *)
(*Set the Base Directory*)


(* ::Input::Initialization:: *)
PackageBaseDirectory=DirectoryName[$InputFileName];


(* ::Section:: *)
(*Get all Submodules*)


(* ::Input::Initialization:: *)
Get[FileNameJoin[{"src","1_fock_states.wl"}]]


(* ::Input::Initialization:: *)
Get[FileNameJoin[{"src","2_ddf_states.wl"}]]


(* ::Input::Initialization:: *)
Get[FileNameJoin[{"src","3_vertex_operator_algebra.wl"}]]


(* ::Input::Initialization:: *)
Get[FileNameJoin[{"src","4_ddf_vertex_operators.wl"}]]


(* ::Input::Initialization:: *)
Get[FileNameJoin[{"src","5_operator_actions.wl"}]]


(* ::Input::Initialization:: *)
Get[FileNameJoin[{"src","6_ground_state_computer.wl"}]]


(* ::Input::Initialization:: *)
Get[FileNameJoin[{"src","7_multi-commutators.wl"}]]


(* ::Section:: *)
(*End Package*)


(* ::Input::Initialization:: *)
Print["Successfully loaded the DDF package."];


(* ::Input::Initialization:: *)
Print["All equations and relations used in this package are derived from the papers [1,2,3] and appropriately adjusted to the Feingold-Frenkel algebra F."];


(* ::Input::Initialization:: *)
Print["[1] R.W. Gebert and H. Nicolai, On E(10) and the DDF construction, Commun. Math. Phys. 172 (1995), 571-622, arXiv:hep-th/9406175."];


(* ::Input::Initialization:: *)
Print["[2] R.W. Gebert and H. Nicolai, An Affine string vertex operator construction at arbitrary level, J. Math. Phys. 38 (1997), 4435-4450, arXiv:hep-th/9608014."];


(* ::Input::Initialization:: *)
Print["[3] S. Capolongo, A. Kleinschmidt, H. Malcha and H. Nicolai, A string-like realization of hyperbolic Kac-Moody algebras, arXiv:2411.18754 [hep-th]."];


(* ::Input::Initialization:: *)
Print[""];


(* ::Input::Initialization:: *)
Print["Copyright (C) 2025 Hannes Malcha"];


(* ::Input::Initialization:: *)
End[]


(* ::Input::Initialization:: *)
EndPackage[]


(* ::Input::Initialization:: *)
Protect["ddf`*"];
