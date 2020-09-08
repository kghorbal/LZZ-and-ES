(* ::Package:: *)

(****
MIT License

Copyright (c) 2020 
Khalil Ghorbal (khalil.ghorbal -at- inria.fr)
and 
Andrew Sogokon (a.sogokon -at- soton.ac.uk)

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE. 
****)


BeginPackage["LZZ`"];

ContinuousInvariantQ::usage="ContinuousInvariantQ[S,f,Q] Implementation of the LZZ decision procedure for checking
whether a semi-algebraic set S is a conitinuous invariant under the flow of a polynomial vector field f with semi-algebraic 
evolution constraint Q. The procedure is originally due to Liu, Zhan and Zhao, EMSOFT 2011 (https://doi.org/10.1145/2038642.2038659)."

Begin["`Private`"]


(* Computes a list REMAINDERS of the derivatives of p after reduction by the REMAINDERS of lower-order derivatives, up to the ORDER of the polynomial p*)
DiffIdeal[p_, f_List, vars_List]:=DiffIdeal[p, f, vars]=Module[{rem=p, GB={p}, L={p}}, (* N.B. using memoization *)
While[ Not[PossibleZeroQ[rem]], (* If the REMAINDER is 0, the ORDER has been attained; STOP *)
rem=PolynomialReduce[(* rem'= *)Grad[rem, vars].f, GB, vars, MonomialOrder -> DegreeReverseLexicographic][[2]];
AppendTo[L, rem]; (* Add the REMAINDER to the list L *)
GB=GroebnerBasis[Join[GB, {rem}], vars, MonomialOrder -> DegreeReverseLexicographic] (* Compute the Gr\[ODoubleDot]bner basis of the augmented list *)
]; (* END WHILE *)
(* Return *) Most[L] ]


Inf[Less[lhs_, rhs_], f_List, vars_List]:= Module[{diffIdeal, diffIdealSublists, p=lhs-rhs},
diffIdeal=DiffIdeal[p, f, vars]; (* An efficient way about computing {p, p', p'',..., p^(ord(p))} *)
diffIdealSublists=Table[diffIdeal[[1;;i]],{i, 1, Length[diffIdeal]}]; (* {{p}, {p, p'}, {p, p', p''},...} *)
Or @@(Map[Function[l, (And @@ Map[#==0 &, Most[l]]) && Last[l]<0], diffIdealSublists]) ]

Inf[Equal[lhs_, rhs_], f_List, vars_List]:= And @@ Map[#==0 &, DiffIdeal[(*p=*)(lhs-rhs), f, vars] ] 

Inf[True, f_List, vars_List]:=True
Inf[False, f_List, vars_List]:=False
Inf[S_, f_List, vars_List]:=S/.{
lhs_==rhs_:> Inf[lhs==rhs, f, vars],
lhs_<rhs_ :> Inf[lhs<rhs, f, vars],
lhs_>rhs_ :> Inf[rhs<lhs, f, vars],
lhs_!=rhs_:> Not[Inf[lhs==rhs, f, vars]],(* Using the property Inf(S^c) = Inf(S)^c of semi-algebraic sets *)
lhs_<=rhs_:> Not[Inf[rhs<lhs, f, vars]], 
lhs_>=rhs_:> Not[Inf[lhs<rhs, f, vars]]}


ContinuousInvariantQ[S_, f_List, vars_List, Q_]:=Module[{cond1, cond2},
(* LZZ conditions *)
cond1 = Implies[ S && Q && Inf[Q, f, vars], (* \[Equal]> *) Inf[S, f, vars] ];
cond2 = Implies[ Not[S] && Q && Inf[Q, -f, vars], (* \[Equal]> *)  Not[Inf[S, -f, vars]] ];
(* Check real arithmetic conditions *)
Reduce[ ForAll[vars, cond1 && cond2 (* Use Simplify[] here to improve performance at your own peril. *)], Reals] ]


End[]
EndPackage[]
