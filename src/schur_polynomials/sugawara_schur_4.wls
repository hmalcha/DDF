#!/usr/bin/env wolframscript
(* ::Package::{808,911}::{{248,Automatic},{144,Automatic}}:: *)

(* ::Input::Initialization:: *)
sugawaraSchurEval[4,level_,p_,sgn_]:=(sgn auxA[level,-4])/(2 Sqrt[2])+1/4 auxA[level,-2]^2+2/3 auxA[level,-3] auxA[level,-1]+(sgn auxA[level,-2] auxA[level,-1]^2)/Sqrt[2]+1/6 auxA[level,-1]^4-2/3 auxA[level,-3] auxA[level,-1] unitRoot[level,p]-Sqrt[2] sgn auxA[level,-2] auxA[level,-1]^2 unitRoot[level,p]-2/3 auxA[level,-1]^4 unitRoot[level,p]-1/2 auxA[level,-2]^2 unitRoot[level,p]^2+auxA[level,-1]^4 unitRoot[level,p]^2-2/3 auxA[level,-3] auxA[level,-1] unitRoot[level,p]^3+Sqrt[2] sgn auxA[level,-2] auxA[level,-1]^2 unitRoot[level,p]^3-2/3 auxA[level,-1]^4 unitRoot[level,p]^3-(sgn auxA[level,-4] unitRoot[level,p]^4)/(2 Sqrt[2])+1/4 auxA[level,-2]^2 unitRoot[level,p]^4+2/3 auxA[level,-3] auxA[level,-1] unitRoot[level,p]^4-(sgn auxA[level,-2] auxA[level,-1]^2 unitRoot[level,p]^4)/Sqrt[2]+1/6 auxA[level,-1]^4 unitRoot[level,p]^4
