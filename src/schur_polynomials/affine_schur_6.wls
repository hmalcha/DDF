#!/usr/bin/env wolframscript
(* ::Package::{808,911}::{{20,Automatic},{Automatic,Automatic}}:: *)

(* ::Input::Initialization:: *)
affineSchurEval[6,level_,sgn_]:=(sgn auxA[level,-6])/(3 Sqrt[2])+1/9 auxA[level,-3]^2+1/4 auxA[level,-4] auxA[level,-2]+(sgn auxA[level,-2]^3)/(12 Sqrt[2])+2/5 auxA[level,-5] auxA[level,-1]+1/3 Sqrt[2] sgn auxA[level,-3] auxA[level,-2] auxA[level,-1]+(sgn auxA[level,-4] auxA[level,-1]^2)/(2 Sqrt[2])+1/4 auxA[level,-2]^2 auxA[level,-1]^2+2/9 auxA[level,-3] auxA[level,-1]^3+(sgn auxA[level,-2] auxA[level,-1]^4)/(6 Sqrt[2])+1/90 auxA[level,-1]^6
