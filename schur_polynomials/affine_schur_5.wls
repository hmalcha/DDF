#!/usr/bin/env wolframscript
(* ::Package::{808,911}::{{20,Automatic},{Automatic,Automatic}}:: *)

(* ::Input::Initialization:: *)
affineSchurEval[5,level_,sgn_]:=(Sqrt[2]*sgn*auxA[level,-5])/5+(auxA[level,-3]*auxA[level,-2])/3+(auxA[level,-4]*auxA[level,-1])/2+(sgn*auxA[level,-2]^2*auxA[level,-1])/(2*Sqrt[2])+(Sqrt[2]*sgn*auxA[level,-3]*auxA[level,-1]^2)/3+(auxA[level,-2]*auxA[level,-1]^3)/3+(sgn*auxA[level,-1]^5)/(15*Sqrt[2])
