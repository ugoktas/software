(* ::Package:: *)

(* :Title: Perturbation Iteration Algorithm *)

(* :Context: PerturbationIterationAlgorithm` *)

(* :Author: Unal Goktas *)

(* :Summary:
    This package is used for carrying out the computations for finding
    perturbation-iteration solutions of differential equations.
*)

(* :Sources:

    Yigit Aksoy, Mehmet Pakdemirli, Saeid Abbasbandy and Hakan Boyaci,
    New perturbation - iteration solutions for nonlinear heat transfer
    equations,
    International Journal of Numerical Methods for Heat and Fluid Flow
    in press.

    Mehmet Pakdemirli, Yigit Aksoy and Hakan Boyaci,
    A new perturbation - iteration approach for first order differential
    equations,
    Mathematical and Computational Applications 16 (2011) 890--899.

    Yigit Aksoy and Mehmet Pakdemirli,
    New perturbation - iteration solutions for Bratu-type equations,
    Computers and Mathematics with Applications 59 (2010) 2802--2808.

    Shih-Hsiang Chang,
    A variational iteration method for solving Troesch's problem,
    Journal of Computational and Applied Mathematics 234 (2010) 3043--3047.

    S. S. Motsa, P. Sibanda, S. Shateyi,
    A new spectral-homotopy analysis method for solving a nonlinear second
    order BVP,
    Commun. Nonlinear Sci. Numer. Simulat 15 (2010) 2293--2302.

    Mehmet Pakdemirli, Hakan Boyaci and H. A. Yurtsever,
    A root-finding algorithm with fifth order derivatives,
    Mathematical and Computational Applications 13 (2008) 123--128.

    Mehmet Pakdemirli, Hakan Boyaci and H. A. Yurtsever,
    Perturbative derivation and comparisons of root-finding algorithms with
    fourth order derivatives,
    Mathematical and Computational Applications 12 (2007) 117--124.

    Mehmet Pakdemirli and Hakan Boyaci,
    Generation of root finding algorithms via perturbation theory and some
    formulas,
    Applied Mathematics and Computation 184 (2007) 783--788.

    Li-Na Zhang and Ji-Huan He,
    Homotopy perturbation method for the solution of the electrostatic
    potential differential equation,
    Mathematical Problems in Engineering 2006 (2006) 1--6.
*)

(* :Copyright: \[Copyright] 2025 by Unal Goktas *)

(* :Package Version: 2.0 *)

(* :Mathematica Version: 8.0 *)

(* :History: Software last updated by Unal Goktas on June 17, 2012 in Ankara, Turkey *)

(* :Keywords: perturbation-iteration *)

(* :Warnings: None *)

(* :Limitations: see on line documentation *)

(* :Discussion: see on line documentation *)

(* :Requirements: None *)

(* :Examples: see on line documentation *)

Print[
   "Loading Package PerturbationIterationAlgorithm.m of June 17, 2012."
];

(*PerturbationIterationAlgorithm`print = Print;*)

System`Private`oldContextPath = System`$ContextPath;

BeginPackage["PerturbationIterationAlgorithm`"];

$ContextPath = Flatten[
	              {
                   "Assumptions`",
                   $ContextPath
                  }
               ];

PerturbationIterationAlgorithm::usage = "PerturbationIterationAlgorithm[{rhs == lhs}, listofinitialconditions, u, t, n, m, step, options] carries out the Perturbation-Iteration Algorithm with n <= m (n: number of correction terms, m: number of terms included in the Taylor series expansion). epsilon is the perturbation parameter. The argument step determines the number of iterations to be carried out. u is the dependent variable and t is the independent variable of the differential equation.";

\[Epsilon]::usage = "\[Epsilon] is the default perturbation parameter.";

PerturbationParameter::usage = "PerturbationParameter is an option for the function PerturbationIterationAlgorithm. It is used for having a perturbation parameter other then \[Epsilon].";

IntroduceEpsilon::usage = "IntroduceEpsilon is an option for the function PerturbationIterationAlgorithm. It is used for controlling the introduction of \[Epsilon].";

GivenUZero::usage = "GivenUZero is an option for the function PerturbationIterationAlgorithm. Its default value is set to Automatic, in which case the function automatically computes UZero. If GivenUZero is set to a user defined expression as GivenUZero -> expr, then expr is used as UZero, and UZero is not computed by the function PerturbationIterationAlgorithm.";

PerturbationIterationAlgorithm::introduce = "An auxiliary perturbation parameter `1` is introduced into the given equation(s). Now, continuing with the equation(s) `2`.";

PerturbationIterationAlgorithm::nointroduce = "No auxiliary perturbation parameter is introduced into the given equation(s). Continuing with the original equation(s).";

PerturbationIterationAlgorithm::solveforuzero1 = "Solving the linear equation(s) `1` for `2` with the condition(s) `3`.";

PerturbationIterationAlgorithm::solveforuzero2 = "Now trying to solve the linear equation(s) `1` for `2` with the condition(s) `3` instead.";

PerturbationIterationAlgorithm::solveforuzero3 = "Using the user defined `1` = `2`.";

PerturbationIterationAlgorithm::approximate = "To eliminate a differential equation with variable coefficients an approximation decision needed to be made. Now, continuing with the equation: \n `1`.";

PerturbationIterationAlgorithm::switch = "Successive iterations started to give same solutions. Hence switching to so called PIA(`1`,`2`) by increasing the included number of terms in the Taylor series expansion.";

$PerturbationIterationAlgorithmTimeConstraint = 100;

Begin["`Private`"];

Options[PerturbationIterationAlgorithm] =
   {
   	PerturbationParameter -> \[Epsilon],
   	IntroduceEpsilon -> True,
   	GivenUZero -> Automatic
   };

PerturbationIterationAlgorithm[eqns_List, ics_List, funs_List, t_, n_Integer,
   m_Integer, step_, opts___?OptionQ] /; (n <= m && MatchQ[eqns, HoldPattern[List[PatternSequence[_ == _]..]]]) :=
   Catch[
      perturbationIterationAlgorithm[eqns, ics, funs, t, n, m, step, opts]
   ]

PerturbationIterationAlgorithm[___] := $Failed

perturbationIterationAlgorithm[eqns_, ics_, funs_, t_, n_, m_, step_,
   opts___] :=
   Block[{f = (#[[1]]-#[[2]]&) /@ eqns, dord, eps, int, K, nn, k, u0, u00, conds, g,
   	  u1, list = {}, p, q, lfuns = funs},
      print["f at point 0 before introduceEpsilon: ", f];
      dord = Max[Cases[{f}, Derivative[i_][q_/; MemberQ[funs, q]][t] :> i, -1]];
      print["dord at point 0: ", dord];
      eps = PerturbationParameter /. {opts} /.
               Options[PerturbationIterationAlgorithm];
      print["eps at point 0: ", eps];
      int = IntroduceEpsilon /. {opts} /.
               Options[PerturbationIterationAlgorithm];
      print["int at point 0: ", int];
      If[int, f = introduceEpsilon[f, funs, t, eps, dord]];
      print["f after introduceEpsilon at point 0: ", f];
      (
       If[int, 
          Message[PerturbationIterationAlgorithm::introduce, eps, StringJoin[ToString[#, StandardForm], " = 0"]& /@ f], 
          Message[PerturbationIterationAlgorithm::nointroduce]
       ];
       K = Unique[K, Temporary];
       nn = Unique[nn, Temporary];
       f = f /. (q_/; MemberQ[funs, q]) :> Function[{x}, q[nn][x]+Sum[eps^k*q[K][k][x], {k, n}]];
       print["f at point 1 after introducing correction terms: ", f];
       f = Normal[Series[f, {eps, 0, m}]];
       print["f at point 2 after Taylor series expansion: ", f];
       f = Flatten[
       	      If[
                 n == 1,
                 {# /. eps -> 1},
                 {
                  Coefficient[#, eps, 0]+Coefficient[#, eps, 1],
                  Table[Coefficient[#, eps, k], {k, 2, n-1}],
                  Sum[Coefficient[#, eps, k], {k, n, m}]
                 }
              ]& /@ f
           ];
       print["Differential system to be solved as eps set to 1: ", f];
       f = Simplify[f];
       print["Simplified version of f: ", f];
       u0 = GivenUZero /. {opts} /. Options[PerturbationIterationAlgorithm];
       If[u0 === Automatic,
          u0 = SolveLinearizedEquation[(#[[1]]-#[[2]]&) /@ eqns, funs, t, dord, ics],
          Message[PerturbationIterationAlgorithm::solveforuzero3, #[0]& /@ funs, u0];
          u0 = {Thread[(#[t]& /@ funs) -> u0]}
       ];
       print["u0: ", u0];
       (
        conds = HomogenizeBoundaryConditions[ics, funs];
        print["homogenized boundary conds: ", conds];
        (
         u0 = u00 = Simplify[Last /@ u0[[1]]];
         print["u0 is taken: ", u00];
         conds = Flatten[(conds /. # &) /@ Thread[(q_/; MemberQ[funs, q]) -> Table[q[K][k], {k, n}]]];
         print["conds for system: ", conds];
         Do[
            g = Union[
                   Simplify[
                      Expand[
                         f /. (Thread[(lfuns /.
                                 (q_/; MemberQ[lfuns, q]) -> q[nn]) -> u0] /.
                                    ((p_ -> q_) :> (p -> Function[Evaluate[q /. t -> #]])))
                      ]
                   ]
                ];
            print["g before DSolve-1: ", g];
            u1 = TimeConstrained[
                    DSolve[Flatten[{Thread[g == 0], conds}],
                       Flatten[Table[funs[[i]][K][k][t], {i, Length[funs]}, {k, n}]],
                       t
                    ],
                    $PerturbationIterationAlgorithmTimeConstraint,
                    $Failed
                 ];
            print["u1 at first attempt: ", u1];
            If[!FreeQ[u1, DSolve | Solve] || Length[u1] == 0,
               print["f before approximation: ", f];
               g = ApproximateEquation[f, funs, t, u00, K, nn];
               print["g after approximation: ", g];
               g = Union[
                      Simplify[Expand[g /.
                         Thread[(#[nn]& /@ funs) -> Map[Function, u0 /. t -> Evaluate[#]]]]
                      ]
                   ];
               print["g before DSolve-2: ", g];
               Block[
                  {$MessagePrePrint = TraditionalForm},
                  Message[PerturbationIterationAlgorithm::approximate,
                     Thread[g == 0]]
               ];
               u1 = DSolve[Flatten[{Thread[g == 0], conds}],
                       Flatten[Table[funs[[i]][K][k][t], {i, Length[funs]}, {k, n}]],
                       t
                    ];
               If[!FreeQ[u1, DSolve | Solve] || Length[u1] == 0, Throw[$Failed]]
            ];
            print["u1 at second attempt: ", u1];
            u1 = Table[Sum[funs[[i]][K][k][t] /. u1[[1]], {k, n}], {i, Length[funs]}];
            print["u1 summed: ", u1];
            If[
               And @@ PossibleZeroQ[u1],
               Message[PerturbationIterationAlgorithm::switch, n, m+1];
               Quiet[
                  Throw[
                     perturbationIterationAlgorithm[{rhs == lhs}, ics, u, t, n,
                        m+1, step]
                  ],
                  {
                   PerturbationIterationAlgorithm::introduce,
                   PerturbationIterationAlgorithm::nointroduce,
                   PerturbationIterationAlgorithm::solveforuzero1,
                   PerturbationIterationAlgorithm::solveforuzero2,
                   PerturbationIterationAlgorithm::solveforuzero3
                  }
               ]
            ];
            u0 = Simplify[u0+u1];
            print["added u0 (result of iteration): ", u0];
            list = Append[list, u0],
            {step}
         ];
         list
        ) /; conds =!= $Failed
       ) /; u0 =!= $Failed
      ) /; f =!= $Failed
   ]

introduceEpsilon[expr_, funs_, t_, eps_, dord_] :=
   Block[{a, b, c},
      b = Flatten[Table[Derivative[i][funs[[j]]][t], {j, Length[funs]}, {i, 0, dord}]];
      print["b at point 1 in introduceEpsilon: ", b];
      a = GroebnerBasis`DistributedTermsList[expr, Union[Variables[expr], b]];
      print["a at point 2 in introduceEpsilon: ", a];
      a = Flatten[Map[(Times @@ MapThread[Power, {a[[2]], #}] &),Map[(#[[1]]&),a[[1]],{2}],{2}]];
      print["a at point 3 in introduceEpsilon: ", a];
      c = Expand[expr];
      print["c at point 4 in introduceEpsilon: ", c];
      a = Select[a, And[!FreeQ[#, q_/; MemberQ[funs, q]], !Internal`LinearQ[#, b], !FreeQ[c, #]]&];
      print["a at point 5 in introduceEpsilon: ", a];
      (
       a = Union[
              Thread[
       	      a -> (a /. {(q_/; MemberQ[funs, q])[t]^i_. :> eps*q[t]^i, 
                 Derivative[j_][(q_/; MemberQ[funs, q])][t]^i_ -> eps*Derivative[j][q][t]^i,
                 Derivative[j_][(q_/; MemberQ[funs, q])][t]^i_.*Derivative[k_][(r_/; MemberQ[funs, r])][t]^l_. :> 
                 eps*Derivative[j][q][t]^i*Derivative[k][r][t]^l})
              ]
           ];
       print["a at point 6 in introduceEpsilon: ", a];
       (c /. a) /. eps^k_ -> eps
      ) /; Length[a] > 0
   ]

introduceEpsilon[___] := $Failed

SolveLinearizedEquation[expr_, funs_, t_, dord_, ics_] :=
   Block[{a, b, c, i},
      b = Flatten[Table[Derivative[i][funs[[j]]][t], {j, Length[funs]}, {i, 0, dord}]];
      print["b at point 1 in SolveLinearizedEquation: ", b];
      a = GroebnerBasis`DistributedTermsList[expr, Union[Variables[expr], b]];
      print["a at point 2 in SolveLinearizedEquation: ", a];
      a = Flatten[Map[(Times @@ MapThread[Power, {a[[2]], #}] &),Map[(#[[1]]&),a[[1]],{2}],{2}]];
      print["a at point 3 in SolveLinearizedEquation: ", a];
      c = Expand[expr];
      a = Select[a, And[!FreeQ[#, q_/; MemberQ[funs, q]], !Internal`LinearQ[#, b], !FreeQ[c, #]]&];
      print["a at point 4 in SolveLinearizedEquation: ", a];
      (
       a = Union[c /. Thread[a -> 0]];
       print["a at point 5 in SolveLinearizedEquation: ", a];
       a = (# == 0 &) /@ a;
       Message[PerturbationIterationAlgorithm::solveforuzero1, a, (#[0]&) /@ funs, ics];
       a = DSolve[Flatten[{a, ics}], (#[t]&) /@ funs, t];
       print["a at point 6 in SolveLinearizedEquation: ", a];
       If[!FreeQ[a, DSolve | Solve] || Length[a] == 0,
          a = (Derivative[dord][#][t] == 0 &) /@ funs;
          Message[PerturbationIterationAlgorithm::solveforuzero2, a, (#[0]&) /@ funs, ics];
          a = DSolve[Flatten[{a, ics}], (#[t]&) /@ funs, t]
       ];
       a /; Length[a] > 0 
      ) /; Length[a] > 0
   ]

SolveLinearizedEquation[___] := $Failed

HomogenizeBoundaryConditions[ics_List, funs_] :=
   Block[{conds, length},
      conds = Cases[ics, (q_/;MemberQ[funs, q])[_] | Derivative[_][q_/;MemberQ[funs, q]][_], -1];
      conds = Solve[ics, conds];
      (
       conds = Flatten[conds];
       length = Length[conds];
       (
        (First[#] == 0 &) /@ conds
       ) /; (length > 0 && length == Length[ics])
      ) /; Length[conds] == 1
   ]

HomogenizeBoundaryConditions[___] := $Failed

ApproximateEquation[f_, funs_, t_, u00_, K_, nn_] :=
   Block[{rules, g, a, k, j, u},
      rules = Thread[(#[nn]& /@ funs) -> Map[Function, u00 /. t -> Evaluate[#]]];
      g = Expand[f] /.
             {
              a_.*(u_/; MemberQ[funs, u])[K][j_][t] :> (a /. rules)*u[K][j][t],
              a_.*Derivative[k_][(u_/; MemberQ[funs, u])[K][j_]][t] :> (a /. rules)*
                 Derivative[k][u[K][j]][t]
             };
      Simplify[g /. (u_/; MemberQ[funs, u])[K][_][t]^a_ :> u00^a]
   ]

End[];

SetAttributes[PerturbationIterationAlgorithm, ReadProtected];

Protect[PerturbationIterationAlgorithm];

EndPackage[];

$ContextPath = Flatten[
	              {
	               "PerturbationIterationAlgorithm`",
                   System`Private`oldContextPath
                  }
               ];

Print["Package PerturbationIterationAlgorithm.m of June 17, 2012 is successfully loaded."];
