type ide = string;;
type exp = Eint of int | Ebool of bool | Den of ide | Prod of exp * exp | Sum of exp * exp | Diff of exp * exp |
	       Eq of exp * exp | Minus of exp | IsZero of exp | Or of exp * exp | And of exp * exp | Not of exp |
	       Ifthenelse of exp * exp * exp | Let of ide * exp * exp | Fun of ide * exp | FunCall of exp * exp |
	       Letrec of ide * exp * exp;;

(* Ambiente polimorfo*)
type 't env= ide->inv;;

let emptyenv (v: 't) = function x->v;;
let applyenv (v: 't env) (i: ide)= r i;;
let bind (v: 't env) (i: ide) (r: 't) = function x -> if x=i then v else applyenv r x;;

(* Tipi esprimibili*)
type evT = Int of int | Bool of bool | Unbound | FunVal of evFun | RecFunVal of ide * evFun
and evFun = ide*exp* evT env

(*rts*)
(*type checking*)
let typecheck (x: string) (v: evT) : Bool = match x with
        |"int" -> (match v with
                    |Int(_)->true
                    | _-> false)
        |"bool" -> (match v with
                    |Bool(_)->true
                    |_->false)
        |_->failwith("not a valid type")
