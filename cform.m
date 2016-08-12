(* Mathematica Package *)
(* Created by Mathematica Plugin for IntelliJ IDEA *)

(* :Title: cform *)
(* :Context: cform` *)
(* :Author: Paul *)
(* :Date: 2016-07-25 *)

(* :Package Version: 0.1 *)
(* :Mathematica Version: *)
(* :Copyright: (c) 2016 Paul *)
(* :Keywords: *)
(* :Discussion: *)

BeginPackage["cform`", {"paul`", "SymbolicC`"}]
(* Exported symbols added here with SymbolName::usage *)

cform
$CFormDefines::usage = "gives a C code fragment of #includes, #defines and inline functions
building up functionality beyond basic C, necessary to make cform expressions
evaluate properly"

CanonicalizeSplitCArgument::usage = "Given a string describing a C type followed
by a variable name, splits it into {{type__String}, identifier_String} and
rearranges const in the type to always be on the right of whatever it qualifies."

CanonicalizeSplitCType::usage = "Given a string describing a C type,
 splits it into {type__String} and
rearranges const in the type to always be on the right of whatever it qualifies."

SymbolicCForm::usage = "Like CForm, but only after ToCCodeString,
and does not treat +, * etc specially for consistency and ease
of parsing/modifying of the resulting code (just Define what the functions mean!)"

CFunctionCallSelf::usage = "Given a function declaration,
generate a CCall of that function with all the same
 argument names. Optionally constructs the CFunction for you,
 and you can leave out the return type."

Begin["`Private`"]

CFunctionCallSelf[CFunction[t_, n_, args_]] := CCall[n,
  Last /@ args
];
CFunctionCallSelf[t_~Optional~"void", n_, args_] :=
    CFunctionCallSelf@CFunction[t, n, args];

SymbolicCForm[f_Symbol[args___]] :=
    CCall[SymbolicCForm@f, SymbolicCForm /@ {args}];

SymbolicCForm::nestedhead =
    "SymbolicCForm does not support nested heads in ``";

SymbolicCForm::numerichead = "Numeric heads detected in ``, unsupported in SymbolicCForm.";
SymbolicCForm[x:_?NumericQ[___]] := (Messages[SymbolicCForm::numerichead,
  x]; $Failed);

SymbolicCForm[
  x : _[___][___]] := (Messages[SymbolicCForm::nestedhead,
  x]; $Failed);

SymbolicCForm[atom_Complex] := CCall["Complex", ReIm@atom];
SymbolicCForm[atom_Symbol] := ToString@atom;
SymbolicCForm[atom_?AtomQ] := atom;


ShiftUpConst[{"const", a_, b___}] := {a, "const", b};
ShiftUpConst[x_] := x;

CanonicalizeSplitCType[s_String] := ShiftUpConst[
  StringTrim@StringSplit[s, WordBoundary] /. "" -> Nothing
]
CanonicalizeSplitCArgument[s_String] /; StringTrim@s === "..." = {{"..."},"..."};

CanonicalizeSplitCArgument[s_String] := MostLast@ShiftUpConst[
  StringTrim@StringSplit[s, WordBoundary] /. "" -> Nothing
]


DPrint[e___] := Null;
(*SparseOptimization`Private`EnableDPrint[] enables redio debugging/logging*)
EnableDPrint[] := DPrint[e___] := Print["cform`: ",e];
DPrint~SetAttributes~HoldAllComplete;


symbolicHead[x_Symbol] := x;
symbolicHead[f_[___]] := symbolicHead@f;
symbolicHead[x_] := Head@x;

hasNestedHeads[x_] :=
    Count[x, _[___][___], {0, Infinity}, Heads -> True] > 0;


hasNumericHeads[x_] :=
    Count[x, _?NumericQ[___], {0, Infinity}, Heads -> True] > 0;


cIdentifierChar = WordCharacter | "_";
dropCContexts[cstr_String] :=
    StringReplace[cstr,
      cIdentifierChar .. ~~ "_" ~~ (x : WordCharacter ..) ~~
          y : Except[cIdentifierChar] :> x <> y];

dropCContexts@"hi_there_my(best_f)" == "my(f)"

(* how to interpret replacements defined below*)
$CFormDefines = "
#include <algorithm>
#include <math.h>
#define rsqrt(x) (1. / sqrt((x)))
inline double sqr(double x) {return x*x;}
#define inv(x) (1. / (x))
#define neg(x) (-(x))
#define times(x,y) ((x)*(y))
#define plus(x,y) ((x)+(y))

#define greater(x,y) ((x)>(y))
#define less(x,y) ((x)<(y))
#define greaterEqual(x,y) ((x)>=(y))
#define lessEqual(x,y) ((x)>=(y))

#define ifthenelse(test,a,b) ((test) ? (a) : (b))

inline double max(int a, double b) { return std::max(double(a), b); }
inline double max(double a, int b) { return std::max(a, double(b)); }
";

cform::nestedhead = "Nested heads detected in ``, unsupported in C.";
cform::numerichead = "Numeric heads detected in ``, unsupported in C.";
cform::unknownSym = "Symbols unknown to C: `` detected in ``";

(* TODO Simplify assuming all variables are real and all functions are real valued? *)
cform[expr_, variableReplacements_List : {},
  extraRules_List : {}] := Module[{
  result = expr /. variableReplacements,
  allRules = Join[extraRules, {
    Sin[x_] :> sin[x],
    Cos[x_] :> cos[x],
    Sqrt[x_?(Not@*TrueQ@*Negative)] :> sqrt[x], (*don't take sqrt of manifest negatives*)
    Abs[x_] :> abs[x],
    (* add more math.h and custom functions here (e.g. Tan[x_] :> tan[x]) and extend defines accordingly *)

    Power[x_, -1/2] :> rsqrt[x],
    Power[x_, 2] :> sqr[x],
    Power[x_, -1] :> inv[x],
    Power[x_, y_] :> pow[x, y],

    Derivative[1][Abs][x_] :> ifthenelse[x < 0, -1, 1], (*good enough*)

    Greater[x_, y_] :> greater[x, y],
    Less[x_, y_] :> less[x, y],
    GreaterEqual[x_, y_] :> greaterEqual[x, y],
    LessEqual[x_, y_] :> lessEqual[x, y],

    Piecewise :> piecewise,
    piecewise[{}, finally_] :> finally,
    piecewise[{{e_, cond_}, rest___}, finally_] :> ifthenelse[
      cond, e, piecewise[{rest}, finally]
    ],

    Times[-1, y_] :> neg[y],
    Times[x_, y_] :> times[x, y],

    Plus[x_, y_] :> plus[x, y],
    Max[x_, y_] :> max[x, y],
    Min[x_, y_] :> min[x, y],
    x_Integer :> x,
    x_?NumericQ :> N[x]
  }]
}, Module[{
  knownSymbols = DeleteDuplicates[
    symbolicHead /@
        Join[Values@variableReplacements,
          Values@allRules, {Real, Integer}]
  ],
  hasNested = False, symbols, hasNumeric = False
},
  DPrint@allRules
  ;DPrint["knownSymbols ", knownSymbols]

  ;DPrint@result
  ;result = result //. allRules
  ;DPrint@result

  ;symbols = (symbolicHead /@ Level[result, {-1}, Heads -> True])
  ;DPrint["ksm ", symbols, knownSymbols~ContainsAll~symbols]
  ;If[
    knownSymbols~ContainsAll~
        symbols && ! (hasNested = hasNestedHeads@result) && ! (hasNumeric = hasNumericHeads@result)


    , (*-- make CForm without any contexts_ -- *)
    dropCContexts@ToString[result // CForm]

    , Which[

      hasNested
      , Message[cform::nestedhead, result]

      , hasNumeric
      , Message[cform::numerichead, result]

      , True
      , Message[cform::unknownSym, FullName /@ Complement[symbols, knownSymbols], result]
    ]; $Failed
  ]
]];

End[] (* `Private` *)

EndPackage[]