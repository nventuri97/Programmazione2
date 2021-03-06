(* Identificatore *)
type ide = string ;;

(* Espressioni *)
type exp = Eint of int | Ebool of bool | Estring of string | Den of ide | Prod of exp * exp | Sum of exp * exp | Diff of exp * exp |
	       Eq of exp * exp | Minus of exp | IsZero of exp | Or of exp * exp | And of exp * exp | Not of exp |
	       Ifthenelse of exp * exp * exp | Let of ide * exp * exp | Fun of ide * exp | FunCall of exp * exp |
	       Letrec of ide * exp * exp | Diz of (ide * exp) list | DizRet of exp * ide | DizRem of exp * ide |
		   DizAdd of exp * ide * exp | DizClear of exp | ApplyOver of exp * exp;;

(* Ambiente polimorfo *)
type 't env = ide -> 't;;
let emptyenv (v: 't) = fun x -> v;;
let applyenv (r: 't env) (i: ide) = r i;;
let bind (r: 't env) (i:ide) (v: 't) = function x -> if x = i then v else applyenv r i;;

(* tipi esprimibili *)
type evT = Int of int | Bool of bool | String of string | Unbound | FunVal of evFun | RecFunVal of ide * evFun |
		   DizVal of (ide * evT) list
and evFun = ide * exp * evT env;;

(*rts*)
(*type checking*)
let typecheck (s: string) (v: evT) : bool = match s with
            "int" -> (match v with
                        Int(_)-> true
                        | _ -> false)
            | "bool" -> (match v with
                        Bool(_)-> true
                        | _ -> false)
			| "string" -> (match v with
						String(_)-> true
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
let rec eval (e: exp) (r: evT env) : evT = match e with
    | Eint x -> Int x
    | Ebool a -> Bool a
	| Estring s -> String s
    | IsZero x -> iszero (eval x r)
    | Den i -> applyenv r i
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
    | Diz(lst) -> let ls = nodup (evalList lst r) in
						DizVal(ls)
    | DizRet(e1, id) -> let d = (eval e1 r) in
                        (match d with
                            DizVal(ls) -> lookup id ls
                            | _ -> failwith("non dictionary value"))
    | DizRem(e1, id) -> let d = (eval e1 r) in
	 					(match d with
							DizVal(ls) -> let ls1 = remove id ls in
											DizVal(ls1)
							| _ -> failwith("non dictionary value"))
	| DizAdd(e1, id, e2) -> let d = (eval e1 r) in
						(match d with
							DizVal(ls) -> if not(inside id ls)
										  then DizVal((id, eval e2 r)::ls)
										  else let ls1 = remove id ls in
												DizVal((id, eval e2 r)::ls1)
							| _ -> failwith("non dictionary value"))
	| DizClear(e1) -> let d = (eval e1 r) in
						(match d with
							DizVal(ls) -> DizVal([])
							| _ -> failwith("non dictionary value"))
	| ApplyOver(f,e1) -> let d = (eval e1 r) in
						match d with
							DizVal(ls) -> let g = (eval f r) in
											let ls1 = apply g ls r in
												DizVal(ls1)
							| _-> failwith("non dictionary value")

(*Funzione per applicare eval alla lista di espressioni in un ambiente r*)
and evalList (lst: (ide * exp) list) (r: evT env) : (ide * evT) list= match lst with
    | [] -> []
    | (x,y)::xs -> (match (x,y) with
                (id, arg) -> (id, eval arg r) :: evalList xs r
                | _ -> failwith("non dictionary value"))
    | _ -> failwith("wrong dictionary list")

(*Funzione che rimuove identificatori duplicati all'interno di una lista*)
and nodup (lst: (ide * evT) list) : (ide * evT) list = match lst with
	[] -> []
	| (x,v)::xs -> if (inside x xs)
	 			   then (x,v)::remove x xs
				   else nodup xs

(*Funzione che ricerca un valore all'interno della lista dato un identificatore*)
and lookup (id: ide) (ls: (ide * evT) list) : evT = match ls with
    [] -> Unbound
    | (id1, x)::ids -> if (id=id1)
					   then x
					   else lookup id ids
    | _ -> failwith("wrong dictionary field")

(*Funzione che rimuove un elemento dalla lista dato un identificatore*)
and remove (id: ide) (ls: (ide * evT) list) : (ide * evT) list = match ls with
	[] -> []
	| (id1,x)::ids -> if(id=id1)
					  then ids
					  else (id1,x) :: (remove id ids)
	| _ -> failwith("wrong dictionary list")

(*Funzione per verificare se un Identificatore è all'interno della lista o meno*)
and inside (id: ide) (ls: (ide * evT) list): bool = match ls with
	[] -> false
	| (x,v)::xs -> if(id=x)
				   then true
				   else inside id xs
	| _ -> failwith("wrong dictionary list")

(*Funzione per applicare la funzione passata come argomento alla lista nell'ambiente r *)
and apply (f: evT) (ls: (ide * evT) list) (r: evT env): (ide * evT) list = match ls with
	[] -> []
	| (id,v)::ids -> (id, funCallEv f v r) :: apply f ids r
	| _ -> failwith("wrong dictionary list")

(*Chiamata di funzione a cui passo la funzione e l'argomento già valutati nell'ambiente*)
and funCallEv (f: evT) (eArg: evT) (r: evT env): evT =
	let fClosure = f in
		(match fClosure with
			FunVal(arg, fBody, fDecEnv)-> eval fBody (bind fDecEnv arg eArg)
			| RecFunVal(g, (arg, fBody, fDecEnv))->
					let rEnv = (bind fDecEnv g fClosure) in
						let aEnv = (bind rEnv arg eArg) in
							eval fBody aEnv);;

(* =================  TESTS  ================= *)

let env0 = emptyenv Unbound;;

(*Creazione dizionario non vuoto*)
let lst = [("nome", Estring "Andrea");("matricola", Eint 555555); ("voto", Eint 30); ("nome", Estring "Carlo")];;
let myDiz = Diz(lst);;
eval myDiz env0;;

(*Clear di myDiz*)
let clear =Let("myDiz2", DizClear(myDiz), Den "myDiz2");;
eval clear env0;;

(*Remove nome da myDiz*)
let rem = Let("myDiz2", myDiz, DizRem(myDiz, "nome"));;
eval rem env0;;

(*Applico a rem la funzione*)
let applyf = Let("myDiz3", ApplyOver(Fun("y", Diff(Den "y", Eint 4)), rem), Den "myDiz3");;
eval applyf env0;;

(*Applico a applyf la funzione*)
let applyf2 = Let("myDiz4", ApplyOver(Fun("y", Ifthenelse(IsZero(Den "y"), Sum(Den "y", Eint 10), Minus(Den "y"))), applyf), Den "myDiz4");;
eval applyf2 env0;;

(*Aggiungo a rem un identificatore nome con valore Giovanni*)
let addV = Let("myDiz4", DizAdd(rem, "nome", Estring "Giovanni"), Den "myDiz4");;
eval addV env0;;

(*Restituisco il valore del nome preso dal dizionario addV*)
let get = DizRet(addV, "nome");;
eval get env0;;

(*Creo un nuovo dizionario vuoto, myDiz2*)
let myDiz2 = Diz([]);;
eval myDiz2 env0;;

(*Aggiungo a myDiz2 l'identificatore nome*)
let addV2 = Let("myDiz2", DizAdd(myDiz2, "nome", Estring "Andrea"), Den "myDiz2");;
eval addV2 env0;;

(*Aggiungo al dizionario addV2 l'identificatore matricola, voto con i relativi valori*)
let addV2 = Let("myDiz2", DizAdd(addV2, "matricola", Eint 1234567), Den "myDiz2");;
eval addV2 env0;;

let addV2 = Let("myDiz3", DizAdd(addV2, "voto", Eint 22), Den "myDiz3");;
eval addV2 env0;;

(*Aggiungo ad addV2 un identificatore nome, ma essendo già presente sostiuirà con il suo valore l'identificatore precedente*)
let addV3 = Let("myDiz5", DizAdd(addV2, "nome", Estring "Marco"), Den "myDiz5");;
eval addV3 env0;;

(*Applico al dizionario addV3 la funzinoe x->x+2*)
let applyf3 = Let("myDiz5", ApplyOver(Fun("x", Sum(Den "x", Eint 2)), addV3), Den "myDiz5");;
eval applyf3 env0;;

(*Restituisco il valore del voto dal dizionario addV3*)
let get2 = DizRet(addV3, "voto");;
eval get2 env0;;
