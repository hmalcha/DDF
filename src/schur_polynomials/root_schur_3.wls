#!/usr/bin/env wolframscript
(* ::Package::{808,676}::{{4,Automatic},{Automatic,4}}:: *)

(* ::Input::Initialization:: *)
rootSchurEval[3,r_]:=1/3 prod[{applyList[toList[r],-3]}]+1/2 prod[{applyList[toList[r],-2],applyList[toList[r],-1]}]+1/6 prod[{applyList[toList[r],-1],applyList[toList[r],-1],applyList[toList[r],-1]}]
