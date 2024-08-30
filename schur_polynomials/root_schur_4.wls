#!/usr/bin/env wolframscript
(* ::Package::{808,676}::{{4,Automatic},{Automatic,4}}:: *)

(* ::Input::Initialization:: *)
rootSchurEval[4,r_]:=1/4 prod[{applyList[toList[r],-4]}]+1/8 prod[{applyList[toList[r],-2],applyList[toList[r],-2]}]+1/3 prod[{applyList[toList[r],-3],applyList[toList[r],-1]}]+1/4 prod[{applyList[toList[r],-2],applyList[toList[r],-1],applyList[toList[r],-1]}]+1/24 prod[{applyList[toList[r],-1],applyList[toList[r],-1],applyList[toList[r],-1],applyList[toList[r],-1]}]
