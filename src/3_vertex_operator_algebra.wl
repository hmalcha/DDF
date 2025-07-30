(* ::Package:: *)

(* ::Title:: *)
(*The Vertex Operator Algebra*)


(* ::Text:: *)
(*This file is part of the DDF Mathematica Package.*)


(* ::Text:: *)
(*Copyright \[Copyright] 2025 Hannes Malcha*)


(* ::Text:: *)
(*The DDF Package is free software: you can redistribute it and/or modify it under the terms of the GNU General Public License as published by the Free Software Foundation, either version 3 of the License, or (at your option) any later version.*)
(*The DDF Package is distributed in the hope that it will be useful, but WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the GNU General Public License for more details.*)
(*You should have received a copy of the GNU General Public License along with the DDF Package. If not, see https://www.gnu.org/licenses/.*)


(* ::Text:: *)
(*The core of the DDF package is the implementation of the vertex operator algebra.*)
(*In particular, the vertex operator algebra allows for the evaluation of commutators of Fock states respectively DDF states.*)
(*Moreover, the vertex operator algebra determines the commutation relations between DDF operators that go into the evaluation of the affine generators, Sugawara operators and coset Virasoro operators.*)


(* ::Text:: *)
(*The commutator between to Fock states is computed by turning one of them into a vertex operator and acting on the other. The commutator between DDF states is evaluated by converting them both to Fock states and subsequently evaluating the commutator of the Fock states.*)


(* ::Section:: *)
(*Public Functions from this Module*)


(* ::Text:: *)
(*sp*)
(*com*)


(* ::Section:: *)
(*Scalar Product of Root Vectors*)


(* ::Text:: *)
(*We introduce the usual scalar product of root vectors spanned by the simple roots r, s and d.*)
(*Make the scalar product bilinear.*)


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
(*Cocycle Factor*)


(* ::Text:: *)
(*In order to make the commutator of vertex operators anti-symmetric we must introduce cocyle factors (see [1]). *)
(*We choose to fix all free cocycle factors to make them disappear from all final expressions.*)


(* ::Text:: *)
(*Make the cocycle factor bi-multiplicative.*)


(* ::Input::Initialization:: *)
eps[Plus[r_,s_],t_]:=eps[r,t]*eps[s,t]
eps[r_,Plus[s_,t_]]:=eps[r,s]*eps[r,t]


(* ::Input::Initialization:: *)
eps[r_,n_?IntegerQ*s_]:=eps[r,Sign[n]*s]^Abs[n]/;Abs[n]!=1
eps[n_?IntegerQ*r_,s_]:=eps[Sign[n]*r,s]^Abs[n]/;Abs[n]!=1
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
eps[d, -r] = eps[d, r];
eps[-d, -s] = eps[d, s];
eps[-d, s] = eps[d, s];
eps[d, -s] = eps[d, s];
eps[-r, -s] = eps[r, s];
eps[-r, s] = eps[r, s];
eps[-r, -s] = eps[r, s];


(* ::Text:: *)
(*Fix the remaining free cocycle factors*)


(* ::Input::Initialization:: *)
eps[d, r]=1;
eps[d,s] = 1;
eps[r, s] =1;


(* ::Section:: *)
(*Product of Creation Operators*)


(* ::Text:: *)
(*In addition to the formal product of elements from the vector space of roots (defined in the fock_states.wl file) we define the formal product of only creation operators from the vector space of roots.*)
(*The use of this product is to remove the wrapper functions op1 and op2 which will be introduced below and to return a prod.*)


(* ::Text:: *)
(*Define the product of creation operators and make it linear, even on formal sums*)


(* ::Input::Initialization:: *)
prodCreation[{ls1___,Plus[a_,b_],ls2___}]:=prodCreation[{ls1,a,ls2}]+prodCreation[{ls1,b,ls2}]
prodCreation[{ls1___,Times[n_?NumericQ,a_],ls2___}]:=n*prodCreation[{ls1,a,ls2}]
prodCreation[{ls1___,Times[z^n_.,a_],ls2___}]:=z^n*prodCreation[{ls1,a,ls2}]
prodCreation[{ls1___,Sum[g_*op1[h_],limits_],ls2___}]:=Sum[g*prodCreation[{ls1,op1[h],ls2}],limits]


(* ::Text:: *)
(*Remove op1 and op2 wrapper functions.*)
(*The use of these is explained below.*)


(* ::Input::Initialization:: *)
prodCreation[{ls1___,op1[u_],ls2___}]:=prodCreation[{ls1,u,ls2}]
prodCreation[{ls1___,op2[u_],ls2___}]:=prodCreation[{ls1,u,ls2}]


(* ::Text:: *)
(*Once all wrapper functions are removed the product is normal ordered and returned as an ordinary prod[...].*)


(* ::Input::Initialization:: *)
prodCreation[ls_]:=prod[Sort[ls]]/;FreeQ[ls,op1]&&FreeQ[ls,op2]


(* ::Section:: *)
(*Vertex Operator*)


(* ::Text:: *)
(*Define the vertex operator of an element u[m] from the vector space of roots  \[CapitalLambda]_\[DoubleStruckCapitalR] according to (2.92)  and  (2.100)  in [1] .*)
(*The u[m] on the right hand side are additionally wrapped in a helper function op1 to distinguish them from the respective elements in the Fock state on which we act.*)


(* ::Input::Initialization:: *)
vertexOp[u_[n_]] := Module[{l}, 
Sum[(((-1)^(n - 1)*(l - n - 1)!)*op1[u[l]]*z^(-l + n))/(l!*(-n - 1)!), {l, 0, Infinity}] + 
    Sum[((l - n - 1)!*op1[u[-l + n]]*z^l)/(l!*(-n - 1)!), {l, 0, Infinity}]]


(* ::Section:: *)
(*The Wrapper Functions*)


(* ::Text:: *)
(*The vertex operator action of one Fock state on another Fock state involves eliminating creation operators u[m] from a product of u[m] by commuting them through to the very right of that product and having them act on the tachyonic state. The u[m] coming from the vertex operator are wrapped in op1 functions. The others are wrapped in op2 functions. We make the wrapper functions linear and introduce the commutation relations between them.*)


(* ::Input::Initialization:: *)
op1[Plus[a_,b_]]:=op1[a]+op1[b]
op1[n_?NumericQ*a_]:=n*op1[a]


(* ::Input::Initialization:: *)
op2[Plus[a_,b_]]:=op2[a]+op2[b]
op2[n_?NumericQ*a_]:=n*op2[a]


(* ::Input::Initialization:: *)
op1[0]:=0


(* ::Text:: *)
(*The commutator between different kinds of u[m] wrapped in either op1 or op2 is called opCom.*)


(* ::Text:: *)
(*Make opCom linear*)


(* ::Input::Initialization:: *)
opCom[0,a_]:=0
opCom[a_,0]:=0


(* ::Input::Initialization:: *)
opCom[n_?NumericQ*a_,b_]:=n*opCom[a,b]
opCom[a_,n_?NumericQ*b_]:=n*opCom[a,b]


(* ::Input::Initialization:: *)
opCom[Plus[a_,b_],c_]:=opCom[a,c]+opCom[b,c]
opCom[a_,Plus[b_,c_]]:=opCom[a,b]+opCom[a,c]


(* ::Input::Initialization:: *)
opCom[Sum[a_*Plus[b_,c_],limits_],d_]:=Sum[a*(opCom[b,d]+opCom[c,d]),limits]


(* ::Text:: *)
(*Give the specific definitions according to (2.73) in [1].*)


(* ::Input::Initialization:: *)
opCom[op1[s_[n_]],op1[u_[m_]]]:=0
opCom[Sum[a_*op1[s_[n_]],limits_],op1[u_[m_]]]:=0
opCom[op1[u_[m_]],Sum[a_*op1[s_[n_]],limits_]]:=0
opCom[Sum[a_*op1[s_[n_]],limits1_],Sum[b_*op1[u_[m_]],limits2_]]:=0


(* ::Input::Initialization:: *)
opCom[op1[s_[n_]],op2[u_[m_]]]:=n*KroneckerDelta[n+m,0]*sp[s,u]


(* ::Input::Initialization:: *)
opCom[Sum[a_*op1[s_[n_]],limits_],op2[u_[m_]]]:=Sum[a*n*KroneckerDelta[n+m,0]*sp[s,u],limits]


(* ::Section:: *)
(*Test for Annihilation Operators*)


(* ::Text:: *)
(*In order to move annihilation operators to the right of creation operators we must know which operators are annihilation operators in the first place. An operator op1[u[n]] is an annihilation operator if n>=0. We implement a test function for this.*)


(* ::Input::Initialization:: *)
annihilatorQ[op1[u_[n_]]]:=If[n>=0,True,False]


(* ::Input::Initialization:: *)
annihilatorQ[op2[u_[n_]]]:=If[n>=0,True,False]


(* ::Text:: *)
(*Return true if at least one operator in a sum of operators is an annihilation operator.*)


(* ::Input::Initialization:: *)
annihilatorQ[Sum[f_*op1[(u_)[n_]], limits_]] := MemberQ[Sum[f*annihilatorQ[op1[u[n]]], limits], True]


(* ::Input::Initialization:: *)
annihilatorQ[a_*Sum[(f_)*op1[(u_)[n_]], limits_]] := MemberQ[Sum[f*annihilatorQ[op1[u[n]]], limits], True]


(* ::Text:: *)
(*Define a few special cases for exponentials, powers and logarithms such as in (2.95) of [1].*)


(* ::Input::Initialization:: *)
annihilatorQ[exp[f_]]:=True


(* ::Input::Initialization:: *)
annihilatorQ[log[1+a_.*Sum[op1[d[-i]]z^i,{i,1,Infinity}]+a_.*Sum[op1[d[i]]z^-i,{i,1,Infinity}]]]:=True


(* ::Input::Initialization:: *)
annihilatorQ[log[1+a_.*Sum[op1[d[-i]]z^i,{i,1,Infinity}]]]:=False


(* ::Input::Initialization:: *)
annihilatorQ[pow[1+a_.*Sum[op1[d[-i]]z^i,{i,1,Infinity}]+a_.*Sum[op1[d[i]]z^-i,{i,1,Infinity}],n_]]:=True


(* ::Input::Initialization:: *)
annihilatorQ[pow[1+a_.*Sum[op1[d[-i]]z^i,{i,1,Infinity}],n_]]:=False


(* ::Text:: *)
(*Check  if  a  list contains at least one annihilation operator.*)


(* ::Input::Initialization:: *)
containsAnnihilatorQ[ls_]:=MemberQ[Map[annihilatorQ,ls],True]


(* ::Section:: *)
(*Sorting and Acting*)


(* ::Text:: *)
(*We define the action of a product of creation and annihilation operators on a tachyonic state.*)
(*The annihilation operators in the product are commuted to the right to act on the tachyonic state until there are no annihilation operators remaining in the product.*)


(* ::Text:: *)
(*If the product is empty we return 1*)


(* ::Input::Initialization:: *)
action[prod[{}],exp[t_]]:=1


(* ::Text:: *)
(*If the product is 0 we return 0*)


(* ::Input::Initialization:: *)
action[0,exp[t_]]:=0


(* ::Text:: *)
(*Make action linear.*)


(* ::Input::Initialization:: *)
action[Plus[a_,b_],exp[t_]]:=action[a,exp[t]]+action[b,exp[t]]
action[f_*prod[ls_],exp[t_]]:=f*action[prod[ls],exp[t]]


(* ::Text:: *)
(*Check if the last operator in the operator product is an annihilation operator. If so apply it to the tachyonic state and then apply the action function again.*)
(*If the last term is not an annihilation operator check if any of the other operators is. If this is true commute one annihilation operator and one creation operator such that the annihilation operator moves to the right. Then apply the action function again.*)
(*If there is no annihilation operator in the list rename prod to prodCreation and do not apply the action function again*)


(* ::Input::Initialization:: *)
action[prod[ls_],exp[t_]]:=If[annihilatorQ[Last[ls]],action[act[prod[ls],exp[t]],exp[t]],If[containsAnnihilatorQ[ls],action[sort[prod[ls]],exp[t]],prodCreation[ls]]]


(* ::Text:: *)
(*Exchange  one creation and one annihilation operator in the product.*)


(* ::Input::Initialization:: *)
sort[prod[{ls1___,a_,b_,ls2___}]]:=opCom[a,b]prod[{ls1,ls2}]+prod[{ls1,b,a,ls2}]/;FreeQ[a,exp]&&FreeQ[a,log]&&FreeQ[a,pow]&&annihilatorQ[a]&&!annihilatorQ[b]


(* ::Text:: *)
(*There are special cases of exponentials, logarithms and powers of u[n] appearing in the product, that stem from the definition of the vertex operator action. *)


(* ::Input::Initialization:: *)
sort[prod[{ls1___,exp[a_],b_,ls2___}]]:=opCom[a,b]prod[{ls1,exp[a],ls2}]+prod[{ls1,b,exp[a],ls2}]/;!annihilatorQ[b]


(* ::Input::Initialization:: *)
sort[prod[{ls1___,log[1+a_],b_,ls2___}]]:=opCom[a,b]prod[{ls1,pow[1+a,-1],ls2}]+prod[{ls1,b,log[1+a],ls2}]/;!annihilatorQ[b]


(* ::Input::Initialization:: *)
sort[prod[{ls1___,pow[1+a_,n_],b_,ls2___}]]:=n*opCom[a,b]prod[{ls1,pow[1+a,n-1],ls2}]+prod[{ls1,b,pow[1+a,n],ls2}]/;!annihilatorQ[b]


(* ::Text:: *)
(*Act  with the last element in the operator product on the second component of the tensor product.*)


(* ::Input::Initialization:: *)
act[prod[{ls___,op1[u_[n_]]}],exp[t_]]:=If[n>0,0,If[n==0,sp[u,t]*prod[{ls}],prod[{ls,op1[u[n]]}]]]


(* ::Text:: *)
(*Again consider the special cases of exponentials, logarithms and powers of u[n].*)


(* ::Input::Initialization:: *)
act[prod[{ls___,exp[_]}],exp[t_]]:=prod[{ls}]


(* ::Input::Initialization:: *)
act[prod[{ls___,log[1+a_.*Sum[op1[d[-i]]z^i,{i,1,Infinity}]+a_.*Sum[op1[d[i]]z^-i,{i,1,Infinity}]]}],exp[t_]]:=prod[{ls,log[1+a*Sum[op1[d[-i]]z^i,{i,1,Infinity}]]}]


(* ::Input::Initialization:: *)
act[prod[{ls___,pow[1+a_.*Sum[op1[d[-i]]z^i,{i,1,Infinity}]+a_.*Sum[op1[d[i]]z^-i,{i,1,Infinity}],n_]}],exp[t_]]:=prod[{ls,pow[1+a*Sum[op1[d[-i]]z^i,{i,1,Infinity}],n]}]


(* ::Text:: *)
(*Also give the action for formal sums of operators.*)


(* ::Input::Initialization:: *)
act[prod[{ls___,Sum[a_*op1[s_[n_]],limits_]}],exp[t_]]:=Sum[a*KroneckerDelta[n,0],limits]*sp[s,t]*prod[{ls}]


(* ::Text:: *)
(*The  definitions above are derived  from (2.117) - (2.120)  in [1] .*)


(* ::Section:: *)
(*Schur Polynomials*)


(* ::Text:: *)
(*The last ingredient for the evaluation of commutators of Fock states are Schur polynomials.*)
(*Some of the more frequently used Schur polynomials are stored in a database and accessed as needed. The others are computed on the spot;.*)


(* ::Text:: *)
(*Define  a  function toList that writes a linear combination of operators (usually roots) into a list*)


(* ::Input::Initialization:: *)
toList[f_]:=Block[{expr=Expand[f]},If[Head[expr]===Symbol,{expr},If[Head[expr]===Times,{expr/.Times->List},expr/.Plus->List/.Times->List]]]


(* ::Text:: *)
(*Define a function applyList that applies a linear combination of operators written as a list {{coeff1, op1}, {coeff2, op2, ...} to some value x. Returns coeff1 op1[x] + coeff2 op2[x] + .... .*)


(* ::Input::Initialization:: *)
applyList[ls_,x_]:=Sum[If[Length[i]==0,Apply[i,{x}],If[Length[i]==2,i[[1]]*Apply[i[[2]],{x}],Message[applyList::nnarg,i];Abort[]]],{i,ls}]


(* ::Input::Initialization:: *)
applyList::nnarg="The argument `1` is not a list of length 2. Aborting evaluation.";


(* ::Text:: *)
(*Give the first few Schur polynomials explicitly*)


(* ::Input::Initialization:: *)
rootSchurEval[m_,r_]:=0/;m<0


(* ::Input::Initialization:: *)
rootSchurEval[0,r_]:=1


(* ::Input::Initialization:: *)
rootSchurEval[1,r_]:=prod[{applyList[toList[r],-1]}]


(* ::Input::Initialization:: *)
rootSchurEval[2,r_]:=1/2 prod[{applyList[toList[r],-1],applyList[toList[r],-1]}]+1/2 prod[{applyList[toList[r],-2]}]


(* ::Text:: *)
(*The longer definitions are read from the database.*)


(* ::Input::Initialization:: *)
Get[FileNameJoin[{PackageBaseDirectory,"src", "schur_polynomials","root_schur_3.wls"}]]


(* ::Input::Initialization:: *)
Get[FileNameJoin[{PackageBaseDirectory,"src", "schur_polynomials","root_schur_4.wls"}]]


(* ::Input::Initialization:: *)
Get[FileNameJoin[{PackageBaseDirectory,"src", "schur_polynomials","root_schur_5.wls"}]]


(* ::Input::Initialization:: *)
Get[FileNameJoin[{PackageBaseDirectory,"src", "schur_polynomials","root_schur_6.wls"}]]


(* ::Input::Initialization:: *)
Get[FileNameJoin[{PackageBaseDirectory,"src", "schur_polynomials","root_schur_7.wls"}]]


(* ::Text:: *)
(*For n > 7 the Schur polynomials are calculated at runtime.*)


(* ::Text:: *)
(*Define an auxiliary product function auxProd to turn products into lists*)


(* ::Input::Initialization:: *)
auxProd[Plus[a_,b_],ls_]:=auxProd[a,ls]+auxProd[b,ls]


(* ::Input::Initialization:: *)
auxProd[n_?NumericQ*a_,ls_]:=n*auxProd[a,ls]


(* ::Input::Initialization:: *)
auxProd[Inactive[applyList][a__],ls_]:=auxProd[1,Append[ls,Inactive[applyList][a]]]


(* ::Input::Initialization:: *)
auxProd[Inactive[applyList][a__]*b_,ls_]:=auxProd[b,Append[ls,Inactive[applyList][a]]]


(* ::Input::Initialization:: *)
auxProd[Power[Inactive[applyList][a__],n_],ls_]:=auxProd[1,Flatten[Append[ls,Table[Inactive[applyList][a],n]]]]


(* ::Input::Initialization:: *)
auxProd[Power[Inactive[applyList][a__],n_]*b_,ls_]:=auxProd[b,Flatten[Append[ls,Table[Inactive[applyList][a],n]]]]


(* ::Text:: *)
(*In the end auxProd is replaced by prod.*)


(* ::Input::Initialization:: *)
auxProd[1,ls_]:=prod[Sort[ls]]


(* ::Text:: *)
(*Give definition of rootSchurEval for n > 7.*)


(* ::Input::Initialization:: *)
rootSchurEval[n_,r_]:=Activate[With[{root=r},Message[rootSchurEval::nnarg];
auxProd[ExpandAll[SeriesCoefficient[Series[Exp[Sum[1/j*Inactive[applyList][Inactive[toList][root],-j]*z^j,{j,1,n}]],{z,0,n}],n]],{}]]]/;n>7


(* ::Input::Initialization:: *)
rootSchurEval::nnarg= "The Schur polynomial necessary for this calculation has not been pre-computed. It is computed now. This might increase the calculation time.";


(* ::Section:: *)
(*Simplify Nested Formal Sums*)


(* ::Text:: *)
(*The vertex operator action introduces products of powers of series and a residue.*)
(*In order to evaluate the residue we must work out the products of these series.*)
(*We define a function sumSimp to work out the product.*)


(* ::Text:: *)
(*If there is only one series do nothing.*)


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
(*Recursively define the simplification of products of series.*)


(* ::Input::Initialization:: *)
sumSimp[Sum[f_. * Sum[g_, limits1_], limits2__]] := If[FreeQ[f, Sum] && FreeQ[g, Sum], Sum[f * g, limits1, limits2], sumSimp[Sum[f * g, limits1,limits2]]]


(* ::Text:: *)
(*Fractions and logarithms of series are expanded as double series.*)
(*Of the outer series only finitely many terms survive the residue. To speed up the calculation we only keep those terms in the double expansion. *)


(* ::Text:: *)
(*Define  sumSimp on terms containing logarithms*)


(* ::Input::Initialization:: *)
sumSimp[Sum[f_.*z^m_ tp[g_.*prodCreation[{ls___,log[1+h_.*Sum[__]]}],exp[t_]],limits2__]]:=Sum[ExpandAll[f*z^m Sum[(-1)^(i1+1)/i1*tp[g*prodCreation[Flatten[{ls,Table[Sum[h*z^i2 d[-i2],{i2,1,-findSummationLimit[m]-i1+1}],i1]}]],exp[t]],{i1,1,-findSummationLimit[m]}]],limits2]/;FreeQ[f,Sum]


(* ::Text:: *)
(*Define  sumSimp on terms containing fractions*)


(* ::Input::Initialization:: *)
sumSimp[Sum[f_.*z^m_ tp[g_.*prodCreation[{ls___,pow[1+h_.*Sum[__],n_]}],exp[t_]],limits2__]]:=Sum[f*z^m tp[g*prodCreation[{ls}],exp[t]],limits2]+Sum[ExpandAll[f*z^m Sum[Binomial[n,i1]*tp[g*prodCreation[Flatten[{ls,Table[Sum[h*z^i2 d[-i2],{i2,1,-findSummationLimit[m]-i1+1}],i1]}]],exp[t]],{i1,1,-findSummationLimit[m]}]],limits2]/;FreeQ[f,Sum]


(* ::Text:: *)
(*The summation limits are computed as follows.*)


(* ::Input::Initialization:: *)
findSummationLimit[n_?NumericQ+b_]:=n+1


(* ::Input::Initialization:: *)
findSummationLimit[b_]:=0/;!NumericQ[b]


(* ::Section:: *)
(*Residue*)


(* ::Text:: *)
(*The last step of computing the commutator of two Fock states or two DDF states is to compute a residue. We define a function that finds the residue of a single power series in z.*)


(* ::Input::Initialization:: *)
res[Plus[f_,g_]]:=res[f]+res[g]
res[Times[f_,Plus[g_,h_]]]:=res[f*g]+res[f*h]
res[n_?NumericQ*Sum[f_,limits__]]:=n*Sum[res[f],limits]
res[Sum[f_,limits__]]:=Sum[res[f],limits]/;FreeQ[f,Sum]


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
(*Commutator*)


(* ::Text:: *)
(*Define  the commutator com between two Fock states respectively two DDF states.*)
(*Similarly to find the Fock state representation of a DDF state it is converted into a multi-commutator ddfCom of DDF operators in their Fock state representation and the tachyonic state.*)
(*These two types of commutators are very similar but the commutator for finding the Fock state representation does not use cocylce factors.*)
(*For easier debugging com and ddfCom are defined side by side.*)


(* ::Text:: *)
(*Both com and ddfCom and take their first argument, turn it into a Vertex operator and act with it on the second argument. The action is computed in terms of all the functions given above.*)


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
(*Convert DDF state to Fock states to evaluate their commutator.*)


(* ::Input::Initialization:: *)
com[ddfProd[a__],b_]:=com[toTp[ddfProd[a]],b]
com[a_,ddfProd[b__]]:=com[a,toTp[ddfProd[b]]]


(* ::Text:: *)
(*com and ddfCom of two general tensor product states.*)


(* ::Input::Initialization:: *)
com[tp[prod[ls1_], exp[r_]], tp[prod[ls2_], exp[t_]]] := 
res[sumSimp[Sum[eps[r, t]*tp[rootSchur[m, r]*z^(m + sp[r, t])*action[prod[Flatten[{exp[Sum[((-(1/n))*op1[applyList[toList[r], n]])/z^n, {n, 1, Infinity}]], Map[vertexOp,ls1],Map[op2,ls2]}]], exp[t]], exp[r + t]], {m, 0, Infinity}]]] /. rootSchur -> rootSchurEval


(* ::Input::Initialization:: *)
ddfCom[tp[prod[ls1_], exp[r_]], tp[prod[ls2_], exp[t_]]] := 
  sortProd[
ExpandAll[res[sumSimp[Sum[tp[rootSchur[m, r]*z^(m + sp[r, t])*action[prod[Flatten[{exp[Sum[((-(1/n))*op1[applyList[toList[r], n]])/z^n, {n, 1, Infinity}]], Map[vertexOp,ls1],Map[op2,ls2]}]], exp[t]], exp[r + t]], {m, 0, Infinity}]]] /. rootSchur -> rootSchurEval]]


(* ::Text:: *)
(*com and ddfCom  of a general state with a tachyonic state.*)


(* ::Input::Initialization:: *)
com[tp[prod[ls1_], exp[r_]], exp[t_]] := 
res[sumSimp[Sum[eps[r, t]*tp[rootSchur[m, r]*z^(m + sp[r, t])*action[prod[Flatten[{exp[Sum[((-(1/n))*op1[applyList[toList[r], n]])/z^n, {n, 1, Infinity}]],Map[vertexOp,ls1]}]], 
          exp[t]], exp[r + t]], {m, 0, Infinity}]]] /. rootSchur -> rootSchurEval


(* ::Input::Initialization:: *)
ddfCom[tp[prod[ls1_], exp[r_]], exp[t_]] := 
  sortProd[
ExpandAll[res[sumSimp[Sum[tp[rootSchur[m, r]*z^(m + sp[r, t])*action[prod[Flatten[{exp[Sum[((-(1/n))*op1[applyList[toList[r], n]])/z^n, {n, 1, Infinity}]], 
         Map[vertexOp,ls1]}]], exp[t]], exp[r + t]], {m, 0, Infinity}]]] /. rootSchur -> rootSchurEval]]


(* ::Text:: *)
(*When exchanging the arguments we do not simply get minus the commutator. Hence we must compute it explicitly.*)


(* ::Input::Initialization:: *)
com[exp[r_], tp[prod[ls2_], exp[t_]]] := 
res[sumSimp[Sum[eps[r, t]*tp[rootSchur[m, r]*z^(m + sp[r, t])*action[prod[Flatten[{exp[Sum[((-(1/n))*op1[applyList[toList[r], n]])/z^n, {n, 1, Infinity}]],Map[op2,ls2]}]], 
          exp[t]], exp[r + t]], {m, 0, Infinity}]]] /. rootSchur -> rootSchurEval


(* ::Input::Initialization:: *)
ddfCom[exp[r_], tp[prod[ls2_], exp[t_]]] := 
  sortProd[
ExpandAll[res[sumSimp[Sum[tp[rootSchur[m, r]*z^(m + sp[r, t])*action[prod[Flatten[{exp[Sum[((-(1/n))*op1[applyList[toList[r], n]])/z^n, {n, 1, Infinity}]], Map[op2,ls2]}]], 
           exp[t]], exp[r + t]], {m, 0, Infinity}]]] /. rootSchur -> rootSchurEval]]


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
ddfCom[longitudinalVirasoroOp[l_, m_], tp[prod[ls2_], exp[t_]]] := 
sortProd[ExpandAll[-ddfCom[tp[prod[{applyList[toList[t], -1]}], exp[(m/l)*d]], tp[prod[ls2], exp[t]]] - 
(m/2)*(res[sumSimp[Sum[tp[rootSchur[n, (m/l)*d]*z^(n + m)*action[prod[Flatten[{log[1 + (1/l)*Sum[op1[d[-i]]*z^i, {i, 1, Infinity}] + (1/l)*Sum[op1[d[i]]/z^i, 
                    {i, 1, Infinity}]], (m/l)*Sum[op1[d[-j]]*z^(j - 1), {j, 1, Infinity}] + (m/l)*Sum[op1[d[j]]*z^(-j - 1), {j, 0, Infinity}], 
                exp[Sum[((-(m/(l*k)))*op1[d[k]])/z^k, {k, 1, Infinity}]], Map[op2,ls2]}]], exp[t]], exp[(m/l)*d + t]], {n, 0, Infinity}]]] /. rootSchur -> rootSchurEval) -      (m/2)*(res[sumSimp[Sum[tp[rootSchur[n, (m/l)*d]*z^(n + m - 1)*action[prod[Flatten[{exp[Sum[((-(m/(l*k)))*op1[d[k]])/z^k, {k, 1, Infinity}]],Map[op2,ls2]}]], exp[t]], 
           exp[(m/l)*d + t]], {n, 0, Infinity}]]] /. rootSchur -> rootSchurEval)]]


(* ::Text:: *)
(*For the action on a tachyonic state we have*)


(* ::Input::Initialization:: *)
ddfCom[longitudinalVirasoroOp[l_,m_],exp[t_]]:=-ddfCom[tp[prod[{applyList[toList[t],-1]}],exp[m/l*d]],exp[t]]-m/2*ReplaceAll[res[ExpandAll[Sum[(-1)^(i-1)/i*tp[prodCreation[Table[Sum[1/l d[-j]z^j,{j,1,-m-i+1}],i]]*(m*z^-1+m/l Sum[prod[{d[-k]}]z^(k-1),{k,1,-m}])*Sum[rootSchur[n,m/l*d]*z^(n+m),{n,0,-m}],exp[m/l*d+t]],{i,1,-m}]]],rootSchur->rootSchurEval]-m/2*tp[rootSchurEval[-m,m/l*d],exp[m/l*d+t]]//ExpandAll//sortProd
