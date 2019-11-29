(*
This is free and unencumbered software released into the public domain.

Anyone is free to copy, modify, publish, use, compile, sell, or
distribute this software, either in source code form or as a compiled
binary, for any purpose, commercial or non-commercial, and by any
means.

In jurisdictions that recognize copyright laws, the author or authors
of this software dedicate any and all copyright interest in the
software to the public domain. We make this dedication for the benefit
of the public at large and to the detriment of our heirs and
successors. We intend this dedication to be an overt act of
relinquishment in perpetuity of all present and future rights to this
software under copyright law.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND,
EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF
MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT.
IN NO EVENT SHALL THE AUTHORS BE LIABLE FOR ANY CLAIM, DAMAGES OR
OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE,
ARISING FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR
OTHER DEALINGS IN THE SOFTWARE.

For more information, please refer to <http://unlicense.org/>
*)

// Types and kinds

type Kind = Star | KFun of Kind * Kind

type BaseTyCon = TyConNumber
               | TyConBool
               | TyConUnit
               | TyConList
               | TyConFun
               | TyConTuple
               | TyConUserDefined of string

type TyCon = TyCon of BaseTyCon * Kind

type TyVar = TyVar of string * Kind

type TyExpr = TVarExpr of TyVar
            | TConExpr of TyCon
            | TApExpr of TyExpr * TyExpr

type Scheme = Forall of ((TyVar list) * TyExpr)

let rec kindStack numTyArgs =
    match numTyArgs with
    | 0 -> Star
    | n -> KFun (Star, kindStack (n - 1))

let tNumber = TConExpr (TyCon (TyConNumber, Star))
let tBool = TConExpr (TyCon (TyConBool, Star))
let tUnit = TConExpr (TyCon (TyConUnit, Star))

let tArrow = TConExpr (TyCon (TyConFun, KFun (Star, KFun (Star, Star))))
let tFun tArg tBody = TApExpr (TApExpr (tArrow, tArg), tBody)

let tComma numArgs = TConExpr (TyCon (TyConTuple, kindStack numArgs))
let tTuple tArgs =
    let numArgs = List.length tArgs
    List.fold
        (fun accumTyExpr tyArg ->
            TApExpr (accumTyExpr, tyArg))
        (tComma numArgs)
        tArgs

// String conversion functions
let baseTyConString b =
    match b with
    | TyConNumber -> "Number"
    | TyConBool -> "Bool"
    | TyConUnit -> "()"
    | TyConUserDefined name -> name
    | _ -> sprintf "%A" b

let parens s = sprintf "(%s)" s

let rec flattenKindChain k =
    match k with
    | KFun (l, r) -> l::(flattenKindChain r)
    | Star -> [k]

let rec kindString k =
    match flattenKindChain k with
    | [Star] -> "*"
    | chain -> List.map (kindString >> parens) chain |> String.concat " -> "

let tyVarString (TyVar (name, _)) = sprintf "'%s" name
let tyConString (TyCon (baseTyCon, _)) = baseTyConString baseTyCon

let flattenTypeAppChain e =
    let rec flattenTypeAppChain' e accum =
        match e with
        | TApExpr (l, r) -> flattenTypeAppChain' l (r::accum)
        | _ -> e::accum
    flattenTypeAppChain' e []

let rec tyExprString e =
    match flattenTypeAppChain e with
    | [TConExpr (TyCon (TyConList, _)); elementTy] ->
        sprintf "[%s]" (tyExprString elementTy)
    | (TConExpr (TyCon (TyConFun, _)))::args ->
        List.map (tyExprString >> parens) args |> String.concat " -> "
    | (TConExpr (TyCon (TyConTuple, _)))::args ->
        List.map tyExprString args |> String.concat ", " |> (sprintf "(%s)")
    | (TVarExpr v)::args ->
        (tyVarString v)::(List.map (tyExprString >> parens) args) |> String.concat " "
    | (TConExpr (TyCon (TyConUserDefined name, _)))::args ->
        name::(List.map (tyExprString >> parens) args) |> String.concat " "
    | [TConExpr (TyCon (baseTyCon, _))] ->
        baseTyConString baseTyCon
    | _ ->
        // Use the F# pretty printer for all other cases
        sprintf "%A" e

let schemeString (Forall (tyvars, tau)) =
    sprintf "∀ %s . %s" (List.map tyVarString tyvars |> String.concat " ") (tyExprString tau)

// Type scheme functions

let rec tysubst theta t =
    match t with
    | TVarExpr u ->
        match Map.tryFind u theta with
        | Some t' -> t'
        | None -> t
    | TApExpr (l, r) ->
        TApExpr (tysubst theta l, tysubst theta r)
    | _ ->
        t

let n = ref 1
let freshpolytyvar kind =
    let ret = TyVar (sprintf "t%i" !n, kind)
    n := !n + 1
    ret

let freshtyvar _ =
    freshpolytyvar Star

let instantiate (Forall (formals, tau)) actuals =
    tysubst (Map.ofList (List.zip formals actuals)) tau

let rec freevars t =
    match t with
    | TVarExpr u -> Set.singleton u
    | TApExpr (l, r) -> Set.union (freevars l) (freevars r)
    | TConExpr _ -> Set.empty

let generalize skipTyVars tau =
    let ts = freevars tau
    Forall (Set.difference ts skipTyVars |> List.ofSeq, tau)

// Constraints

type ErrorMessage = Lazy<string>

type Constraint = Equal of TyExpr * TyExpr * ErrorMessage
                | And of Constraint * Constraint
                | Trivial

let (=~=) q1 q2 err = Equal (q1, q2, err)
let (&&&) c1 c2 = And (c1, c2)

let rec conjoinConstraints cc =
    match cc with
    | [] -> Trivial
    | [c] -> c
    | c::cs -> c &&& (conjoinConstraints cs)

// Solver
exception TypeError of string

// Some useful extensions to F#'s map module
module Map =
    let keys m = m |> Map.toSeq |> Seq.map fst |> Set.ofSeq

    let fromKeys f keys =
        Seq.fold (fun accum k -> Map.add k (f k) accum) Map.empty keys

    let singleton key value =
        Map.add key value Map.empty

type Subst = Map<TyVar, TyExpr>
let idSubst : Subst = Map.empty

let varsubst theta (v : TyVar) : TyExpr =
    match Map.tryFind v theta with
    | Some tau -> tau
    | None -> TVarExpr v

let compose (theta2 : Subst) (theta1 : Subst) =
    let domain = Set.union (Map.keys theta2) (Map.keys theta1)
    let replaceTheta = (varsubst theta1) >> (tysubst theta2)
    Map.fromKeys replaceTheta domain

let rec consubst theta con =
    match con with
    | Equal (tau1, tau2, err) ->
        let ts = tysubst theta
        Equal (ts tau1, ts tau2, err)
    | And (c1, c2) ->
        And (consubst theta c1, consubst theta c2)
    | Trivial ->
        Trivial

let (|--->) (a : TyVar) (tau : TyExpr) =
    match tau with
    | TVarExpr b ->
        if a = b then
            Some idSubst
        else
            let (TyVar (_, kindA)) = a
            let (TyVar (_, kindB)) = b
            if kindA = kindB then
                Some (Map.singleton a tau)
            else
                None
    | _ ->
        if Set.contains a (freevars tau) then
            None
        else
            Some (Map.singleton a tau)

let rec solve (con : Constraint) : Subst =
    match con with
    | Trivial -> idSubst
    | And (left, right) ->
        let theta1 = solve left
        let theta2 = solve (consubst theta1 right)
        compose theta2 theta1
    | Equal (tau1, tau2, err) ->
        let failMsg = lazy (sprintf "Type error: The types %s and %s are not equal.\n\n%s" (tyExprString tau1) (tyExprString tau2) (err.Force()))
        match (tau1, tau2) with
        | ((TVarExpr a, tau') | (tau', TVarExpr a)) ->
            match (a |---> tau') with
            | Some answer -> answer
            | None -> raise <| TypeError (failMsg.Force())
        | (TConExpr mu, TConExpr mu') ->
            if mu = mu' then
                idSubst
            else
                raise <| TypeError (failMsg.Force())
        | (TApExpr (l, r), TApExpr (l', r')) ->
            solve (((l =~= l') err) &&& ((r =~= r') err))
        | _ ->
            raise <| TypeError (failMsg.Force())

[<EntryPoint>]
let main argv =
    let solveAndCatch con =
        try
            printf "%A\n\n" (solve con)
        with
            | TypeError s ->
                printf "%s" s
    let t1 = tTuple [freshtyvar () |> TVarExpr; tNumber]
    let t2 = tTuple [tUnit; freshtyvar () |> TVarExpr]
    let con1 = (t1 =~= t2) (lazy ("Tuples aren't equal"))
    solveAndCatch con1
    let con2 = (tUnit =~= tNumber) (lazy ("Clearly unit isn't the same type as a number"))
    solveAndCatch con2
   0 
