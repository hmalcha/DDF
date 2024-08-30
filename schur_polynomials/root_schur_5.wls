#!/usr/bin/env wolframscript
(* ::Package::{808,676}::{{4,Automatic},{Automatic,4}}:: *)

(* ::Input::Initialization:: *)
rootSchurEval[5,r_]:=1/5 prod[{applyList[toList[r],-5]}]+1/6 prod[{applyList[toList[r],-3],applyList[toList[r],-2]}]+1/4 prod[{applyList[toList[r],-4],applyList[toList[r],-1]}]+1/8 prod[{applyList[toList[r],-2],applyList[toList[r],-2],applyList[toList[r],-1]}]+1/6 prod[{applyList[toList[r],-3],applyList[toList[r],-1],applyList[toList[r],-1]}]+1/12 prod[{applyList[toList[r],-2],applyList[toList[r],-1],applyList[toList[r],-1],applyList[toList[r],-1]}]+1/120 prod[{applyList[toList[r],-1],applyList[toList[r],-1],applyList[toList[r],-1],applyList[toList[r],-1],applyList[toList[r],-1]}]
