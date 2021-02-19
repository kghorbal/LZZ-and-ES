(* ::Package:: *)

(****
MIT License

Copyright (c) 2020-2021 
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


(** 
  Package implementing the ExitSet-based criterion for checking the invariance 
  of semi-algebraic sets for polynomial vector fields. 
**)


BeginPackage["ESE`"];


ContinuousInvariantQ::"ContinuousInvariantQ[S, f, vars, Q] Checks whether S is a positively invariant set for f under the constraint Q "


Begin["`Private`"]


(* Computes the differential ideal of p -- uses memoization *)
DiffIdeal[p_, f_List, vars_List]:=DiffIdeal[p, f, vars]=Module[{rem=p, GB={p}, L={p}}, (* N.B. using memoization *)
While[Not[PossibleZeroQ[rem]],
rem=PolynomialReduce[(* rem'=*)Grad[rem,vars].f, GB, vars, MonomialOrder -> DegreeReverseLexicographic][[2]];
AppendTo[L,rem];
GB=GroebnerBasis[Join[GB,{rem}], vars, MonomialOrder -> DegreeReverseLexicographic];
]; (* END WHILE *)
(* Return all but the last element *) Most[L] 
]


Inf[Less[lhs_, rhs_], f_List, vars_List]:= Module[{diffIdeal, diffIdealSublists, p=lhs-rhs},
diffIdeal=DiffIdeal[p, f, vars]; (* An efficient way about computing {p, p', p'',..., p^(ord(p))} *)
diffIdealSublists=Table[diffIdeal[[1;;i]],{i, 1, Length[diffIdeal]}]; (* {{p}, {p, p'}, {p, p', p''},...} *)
Or @@(Map[Function[l, (And @@ Map[#==0 &, Most[l]]) && Last[l]<0], diffIdealSublists]) ]

Inf[Equal[lhs_, rhs_], f_List, vars_List]:= And @@ Map[#==0 &, DiffIdeal[(*p=*)(lhs-rhs), f, vars] ] 

Inf[True, f_List, vars_List]:=True
Inf[False, f_List, vars_List]:=False
Inf[S_, f_List, vars_List]:=S/.{
lhs_<rhs_ :> Inf[lhs<rhs, f, vars],
lhs_>rhs_ :> Inf[rhs<lhs, f, vars],
lhs_==rhs_:> Inf[lhs==rhs, f, vars],
lhs_<=rhs_:> Not[Inf[rhs<lhs, f, vars]], (* Using the property Inf(S^c) = Inf(S)^c of semi-algebraic sets *)
lhs_>=rhs_:> Not[Inf[lhs<rhs, f, vars]],
lhs_!=rhs_:> Not[Inf[lhs==rhs, f, vars]]}


Neg[True]:=False
Neg[False]:=True
Neg[!S_]:=S
Neg[S1_ && S2_]:=(!S1) || (!S2)
Neg[S1_ || S2_]:=(!S1) && (!S2)
(* Negate inequlities and equalities. The LogicalExpand is required for Implies, Xor, as well as expressions of the form a<b<c *) 
Neg[S_]:= LogicalExpand[!S] 


Exitf[lhs_==rhs_, f_List, vars_List]:=Exitf[lhs==rhs, f, vars]=Module[{i,n,L,p=lhs-rhs},
L=DiffIdeal[p,f,vars];
n=Length[L];
If[n<2,False,
Or @@ Map[Function[L,(And @@ Map[#==0&,L[[1;;-2]]]) && Last[L]!=0],Table[Take[L,i],{i,2,n}]]
]]


Exitf[lhs_<=rhs_,f_List,vars_List]:=Exitf[lhs<=rhs,f,vars]=Module[{i,n,L,p=lhs-rhs},
L=DiffIdeal[p,f,vars];
n=Length[L];
If[n<2,False,
Or @@ Map[Function[L,(And @@ Map[#==0&,L[[1;;-2]]]) && Last[L]>0],Table[Take[L,i],{i,2,n}]]
]]


NonEmpty[False, R_, f_List, vars_List] := False
NonEmpty[True, R_, f_List, vars_List] := False
NonEmpty[lhs_<rhs_, R_, f_List, vars_List] := False
NonEmpty[lhs_>rhs_, R_, f_List, vars_List] := False
NonEmpty[lhs_!=rhs_, R_, f_List, vars_List] := False
NonEmpty[lhs_==rhs_, R_, f_List, vars_List] := Reduce[Exists[vars,Exitf[lhs==rhs,f,vars] && R],vars,Reals]
NonEmpty[lhs_<=rhs_, R_, f_List, vars_List] := Reduce[Exists[vars,Exitf[lhs<=rhs,f,vars] && R],vars,Reals]
NonEmpty[lhs_>=rhs_, R_, f_List, vars_List] := Reduce[Exists[vars,Exitf[-lhs<=-rhs,f,vars] && R],vars,Reals]
NonEmpty[S1_ || S2_, R_, f_List, vars_List] := NonEmpty[S1, R&&(!Inf[S2,f,vars]), f, vars] ||  NonEmpty[S2, R&&(!Inf[S1,f,vars]), f, vars]
NonEmpty[S1_ && S2_, R_, f_List, vars_List] := NonEmpty[S1, R&&S2, f, vars] ||  NonEmpty[S2, R&&S1, f, vars]
NonEmpty[!S_, R_, f_List, vars_List] := NonEmpty[Neg[S], R, f, vars]


ContinuousInvariantQ[S_,f_List,vars_List,Q_]:=Module[{},
!(NonEmpty[S,Q&&Inf[Q,f,vars],f,vars] || NonEmpty[!S,Q&&Inf[Q,-f,vars],-f,vars])
]


End[]
EndPackage[]
