(* Identificatore *)
type ide = string ;;

(* Espressioni *)
type exp = Eint of int | Ebool of bool | Den of ide | Prod of exp * exp | Sum of exp * exp | Diff of exp * exp |
	       Eq of exp * exp | Minus of exp | IsZero of exp | Or of exp * exp | And of exp * exp | Not of exp |
	       Ifthenelse of exp * exp * exp | Let of ide * exp * exp | Fun of ide * exp | FunCall of exp * exp |
	       Letrec of ide * exp * exp;;

(* Ambiente polimorfo *)
type 't env = ide -> 't;;
let emptyenv (v: 't) = fun x -> v;;
let applyenv (r: 't env) (i: ide) = r i;;
let bind (r: 't env) (i:ide) (v: 't) = function x -> if x = i then v else applyenv r i;;

(* tipi esprimibili *)
type evT = Int of int | Bool of bool | Unbound | FunVal of evFun | RecFunVal of ide * evFun
and evFun = ide * exp * evT env

(*rts*)
(*type checking*)
let typecheck (s: string) (v: evT) : bool = match s with
            "int" -> (match v with
                        Int(_)-> true
                        | _ -> false)
            | "bool" -> (match v with
                        Bool(_)-> true
                        | _ -> false)
            | _ -> failwith("not a valid type");;

(*funzioni primitive*)
