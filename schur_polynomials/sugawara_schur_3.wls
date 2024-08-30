#!/usr/bin/env wolframscript
(* ::Package::{808,911}::{{52,Automatic},{Automatic,124}}:: *)

(* ::Input::Initialization:: *)
sugawaraSchurEval[3,level_,p_,sgn_]:=1/3 Sqrt[2] sgn auxA[level,-3]+auxA[level,-2] auxA[level,-1]+1/3 Sqrt[2] sgn auxA[level,-1]^3-auxA[level,-2] auxA[level,-1] unitRoot[level,p]-Sqrt[2] sgn auxA[level,-1]^3 unitRoot[level,p]-auxA[level,-2] auxA[level,-1] unitRoot[level,p]^2+Sqrt[2] sgn auxA[level,-1]^3 unitRoot[level,p]^2-1/3 Sqrt[2] sgn auxA[level,-3] unitRoot[level,p]^3+auxA[level,-2] auxA[level,-1] unitRoot[level,p]^3-1/3 Sqrt[2] sgn auxA[level,-1]^3 unitRoot[level,p]^3
