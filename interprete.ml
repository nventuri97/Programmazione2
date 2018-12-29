(* Identificatore *)
type ide = string ;;

(* Espressioni *)
type exp = Eint of int | Ebool of bool | Den of ide | Prod of exp * exp | Sum of exp * exp | Diff of exp * exp |
	       Eq of exp * exp | Minus of exp | IsZero of exp | Or of exp * exp | And of exp * exp | Not of exp |
	       Ifthenelse of exp * exp * exp | Let of ide * exp * exp | Fun of ide * exp | FunCall of exp * exp |
	       Letrec of ide * exp * exp | Diz of (ide * exp) list | Ret of exp*ide;;

(* Ambiente polimorfo *)
type 't env = ide -> 't;;
let emptyenv (v: 't) = fun x -> v;;
let applyenv (r: 't env) (i: ide) = r i;;
let bind (r: 't env) (i:ide) (v: 't) = function x -> if x = i then v else applyenv r i;;

(* tipi esprimibili *)
type evT = Int of int | Bool of bool | Unbound | FunVal of evFun | RecFunVal of ide * evFun | DizVal of (ide * evT) list
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
let prod x y = if (typecheck "int" x) && (typecheck "int" y)
               then (match (x,y) with
                    (Int(n),Int(m))-> Int(n*m))
               else failwith("Type error");;

let sum x y = if (typecheck "int" x) && (typecheck "int" y)
               then (match (x,y) with
                    (Int(n),Int(m))-> Int(n+m))
               else failwith("Type error");;

let diff x y = if (typecheck "int" x) && (typecheck "int" y)
               then (match (x,y) with
                    (Int(n),Int(m))-> Int(n-m))
               else failwith("Type error");;

let eq x y = if (typecheck "int" x) && (typecheck "int" y)
             then (match (x,y) with
                    (Int(n),Int(m))-> Bool(n=m))
             else failwith("Type error");;

let minus x = if (typecheck "int" x)
              then (match x with
                    Int(n)-> Int(-n))
              else failwith("Type error");;

let iszero x = if (typecheck "int" x)
               then (match x with
                    Int(n) -> Bool(n=0))
               else failwith("Type error");;

let oR a b = if (typecheck "bool" a) && (typecheck "bool" b)
             then (match (a,b) with
                    (Bool(n),Bool(m))-> Bool(n||m))
             else failwith("Type error");;

let aNd a b = if (typecheck "bool" a) && (typecheck "bool" b)
              then (match (a,b) with
                    (Bool(n),Bool(m))-> Bool(n&&m))
              else failwith("Type error");;

let non a = if (typecheck "bool" a)
            then (match a with
                    Bool(true)-> Bool(false)
                    | Bool(false) -> Bool(true))
            else failwith("Type error");;

(*Interprete*)
let eval (e: exp) (r: evT env) : evT = match e with
    | Eint x -> Int x
    | Ebool a -> Bool a
    | Den i -> applyenv r i
    | IsZero a -> iszero (eval a r)
    | Prod(x,y) -> prod (eval x r) (eval y r)
    | Sum(x,y) -> sum (eval x r) (eval y r)
    | Diff(x,y) -> diff (eval x r) (eval y r)
    | Eq (x,y) -> eq (eval x r) (eval y r)
    | Minus x -> minus (eval x r)
    | And(a,b) -> aNd (eval a r) (eval b r)
    | Or(a,b) -> oR (eval a r) (eval b r)
    | Not a -> non (eval a r)
    | Ifthenelse(e1,e2,e3) -> let g = (eval e1 r) in
              if (typecheck "bool" g)
                then (if (g=Bool(true)) then (eval e2 r) else (eval e3 r))
                else failwith("Non boolean guard")
    | Let(i,e1,e2) -> eval e2 (bind r i (eval e1 r))
    | Fun(i,a) -> FunVal(i,a,r)
    | FunCall(f, eArg) ->
        let fClosure = (eval f r) in
            (match fClosure with
                FunVal(arg, fBody, fDecEnv)-> eval fBody (bind fDecEnv arg (eval eArg r))
                | RecFunVal(g, (arg, fBody, fDecEnv))->
                    let aVal = (eval eArg r) in
                        let rEnv = (bind fDecEnv g fClosure) in
                            let aEnv = (bind rEnv arg aVal) in
                                eval fBody aEnv
                | _ -> failwith("non functional value"))
    | Letrec(f, funDef, letBody) ->
        		(match funDef with
            		Fun(i, fBody) -> let r1 = (bind r f (RecFunVal(f, (i, fBody, r)))) in
                         			                eval letBody r1 |
            		_ -> failwith("non functional def"))
    | Diz(lst) -> DizVal(evalList lst r)
    | Ret(e1, lst, i) -> let d = (eval e1 r) in
                        (match d with
                            DizVal(lst)-> 
                            | _ -> failwith("not a dictionary"))

and evalList (lst: (ide*exp) list) (r: evT env) : evT = match lst with
    []->[]
    | x::xs -> (match (eval x r) with
                (id, arg) -> (id, eval arg r) :: evalList xs r
                | _ -> failwith("wrong dictionary pair"))
    | _ -> failwith("wrong dictionary list")
