#!/usr/bin/env wolframscript
(* ::Package::{808,911}::{{20,Automatic},{Automatic,Automatic}}:: *)

(* ::Input::Initialization:: *)
affineSchurEval[7,level_,sgn_]:=1/7 Sqrt[2] sgn auxA[level,-7]+1/6 auxA[level,-4] auxA[level,-3]+1/5 auxA[level,-5] auxA[level,-2]+(sgn auxA[level,-3] auxA[level,-2]^2)/(6 Sqrt[2])+1/3 auxA[level,-6] auxA[level,-1]+1/9 Sqrt[2] sgn auxA[level,-3]^2 auxA[level,-1]+(sgn auxA[level,-4] auxA[level,-2] auxA[level,-1])/(2 Sqrt[2])+1/12 auxA[level,-2]^3 auxA[level,-1]+1/5 Sqrt[2] sgn auxA[level,-5] auxA[level,-1]^2+1/3 auxA[level,-3] auxA[level,-2] auxA[level,-1]^2+1/6 auxA[level,-4] auxA[level,-1]^3+(sgn auxA[level,-2]^2 auxA[level,-1]^3)/(6 Sqrt[2])+(sgn auxA[level,-3] auxA[level,-1]^4)/(9 Sqrt[2])+1/30 auxA[level,-2] auxA[level,-1]^5+(sgn auxA[level,-1]^7)/(315 Sqrt[2])
