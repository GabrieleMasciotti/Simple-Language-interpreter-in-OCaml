
(*Tutte le spiegazioni e commenti sono forniti nella relazione allegata al progetto, in modo da mantenere pulito il codice.*)

type ide = string;;

type exp =
| CstInt of int
| CstTrue
| CstFalse
| Times of exp * exp
| Sum of exp * exp
| Sub of exp * exp
| Eq of exp * exp
| Iszero of exp
| Or of exp * exp
| And of exp * exp
| Not of ide
| Den of ide
| Ifthenelse of exp * exp * exp
| Let of ide * exp * exp
| Fun of ide * exp
| Apply of exp * exp
| Letrec of ide * ide * exp * exp
| Diz of expdiz
| Search of ide * exp
| Insert of ide * exp * exp
| Delete of ide * exp
| Iterate of exp * exp
| Fbin of ide * ide * exp
| LetrecBin of ide * ide * ide * exp * exp
| Applybin of exp * exp * exp
| Fold of exp * exp
| Filter of ide list * exp
and expdiz = 
	|DizVuotoexp
	|List of (ide * exp) * expdiz;;

module type ENV =
sig
type 't env
val emptyenv : 't -> 't env
val bind : 't env * string * 't -> 't env
val bindlist : 't env * (string list) * ('t list) -> 't env
val applyenv : 't env * string -> 't
exception WrongBindlist
end;;

module Listenv: ENV =
struct
type 't env = (string * 't) list
exception WrongBindlist
let emptyenv(x) = [("", x)]
let rec applyenv(x, y) = (match x with
	| [(r,e)] -> if y = r then e else failwith("wrong env")
	| (i1, e1) :: x1 -> if y = i1 then e1 else applyenv(x1, y)
	| [] -> failwith("wrong env"))
let bind(r, l, e) = (l, e) :: r
let rec bindlist(r, il, el) = match (il, el) with
| ([], []) -> r
| (i::il1, e::el1) -> bindlist (bind(r, i, e), il1, el1)
| _ -> raise WrongBindlist
end;;

open Listenv;;

type evT = | Int of int | Bool of bool | Unbound
| Closure of ide * exp * evT env
| RecClosure of ide * ide * exp * evT env
| ClosureBin of ide * ide * exp * evT env
| RecClosureBin of ide * ide * ide * exp * evT env
| Dizionario of evTdiz
and evTdiz =
	|DizVuoto
	|RestoDiz of (ide * evT) * evTdiz;;

(*Type checker*)
let typecheck (x, y) =
match x with
| "int" ->
(match y with
| Int(u) -> true
| _ -> false)
| "bool" ->
(match y with
| Bool(u) -> true
| _ -> false)
| "diz" -> 
(match y with
| Dizionario(u) -> true
| _ -> false)
| _ -> failwith ("not a valid type");;

let is_zero x = match (typecheck("int",x), x) with
| (true, Int(y)) -> Bool(y=0)
| (_, _) -> failwith("run-time error");;

let int_eq(x,y) =
match (typecheck("int",x), typecheck("int",y), x, y) with
| (true, true, Int(v), Int(w)) -> Bool(v = w)
| (_,_,_,_) -> failwith("run-time error");;

let int_plus(x, y) =
match(typecheck("int",x), typecheck("int",y), x, y) with
| (true, true, Int(v), Int(w)) -> Int(v + w)
| (_,_,_,_) -> failwith("run-time error");;

let int_sub(x, y) =
match(typecheck("int",x), typecheck("int",y), x, y) with
| (true, true, Int(v), Int(w)) -> Int(v - w)
| (_,_,_,_) -> failwith("run-time error");;

let int_times(x, y) =
match(typecheck("int",x), typecheck("int",y), x, y) with
| (true, true, Int(v), Int(w)) -> Int(v * w)
| (_,_,_,_) -> failwith("run-time error");;

let bool_and(x, y) =
match(typecheck("bool",x), typecheck("bool",y), x, y) with
| (true, true, Bool(v), Bool(w)) -> Bool(v && w)
| (_,_,_,_) -> failwith("run-time error");;

let bool_or(x, y) =
match(typecheck("bool",x), typecheck("bool",y), x, y) with
| (true, true, Bool(v), Bool(w)) -> Bool(v || w)
| (_,_,_,_) -> failwith("run-time error");;

let bool_not(x) =
if (typecheck("bool", x)=true) then 
	if x = Bool(false) then Bool(true) else Bool(false)
else failwith("run-time error");;


let rec has_key(iden, diz) = match diz with
	|DizVuoto -> false
	|RestoDiz((i,e),rest) -> if iden = i then true else has_key(iden,rest);;

let insert(iden, valr, dict) = if typecheck("diz",dict) = false then failwith("not a dictionary") else
	match (iden, typecheck("int",valr)) with
		|("", _) -> failwith ("empty name not accepted")
		|(_, true) -> (match dict with 
			|Dizionario(x) -> (match x with
				|DizVuoto -> Dizionario(RestoDiz((iden,valr),DizVuoto))
				|RestoDiz((c,v),z) ->
					if typecheck("int",v) then Dizionario(RestoDiz((iden,valr),RestoDiz((c,v),z))) else failwith("not homogeneous element type"))
			|_ -> failwith("not a dictionary"))
		|(_,false) -> (match dict with 
			|Dizionario(x) -> (match x with
				|DizVuoto -> Dizionario(RestoDiz((iden,valr),DizVuoto))
				|RestoDiz((c,v),z) ->
					if typecheck("bool",v) then Dizionario(RestoDiz((iden,valr),RestoDiz((c,v),z))) else failwith("not homogeneous element type"))
			|_ -> failwith("not a dictionary"));;

let rec remove(i, diz) = match diz with
	|DizVuoto -> DizVuoto
	|RestoDiz((c,v),z) -> if i = c then z else RestoDiz((c,v), (remove(i,z)));;

let rec lookup_list(lista,elem) = match lista with
	|[] -> false
	|x::xs -> if x=elem then true else lookup_list(xs,elem);;

let rec filter(lista,diz) = match diz with
	|DizVuoto -> DizVuoto
	|RestoDiz((c,v),z) -> if lookup_list(lista,c) = false then filter(lista,z) else RestoDiz((c,v),filter(lista,z));;


let rec eval (e:exp) (amb: evT env) : evT = match e with
| CstInt(n) -> Int(n)
| CstTrue -> Bool(true)
| CstFalse -> Bool(false)
| Den(s) -> applyenv(amb,s)
| Let(i, e, ebody) -> eval ebody (bind (amb, i, (eval e amb)))
| Letrec(f, i, fBody, letBody) -> let benv = bind(amb, f, (RecClosure(f, i, fBody, amb))) in eval letBody benv
| LetrecBin(f, i1, i2, fBody, letBody) -> let benv = bind(amb, f, (RecClosureBin(f, i1, i2, fBody, amb))) in eval letBody benv
| Sum(e1, e2) -> int_plus ((eval e1 amb), (eval e2 amb))
| Sub(e1, e2) -> int_sub ((eval e1 amb), (eval e2 amb))
| Iszero(e1) -> is_zero(eval e1 amb)
| Eq(e1, e2) -> int_eq((eval e1 amb), (eval e2 amb))
| Times(e1,e2) -> int_times((eval e1 amb), (eval e2 amb))
| And(e1, e2) -> bool_and((eval e1 amb), (eval e2 amb))
| Or(e1, e2) -> bool_or ((eval e1 amb), (eval e2 amb))
| Not(e1) -> bool_not(applyenv(amb,e1))
| Ifthenelse(cond,e1,e2) -> (
	let g = eval cond amb in match (typecheck("bool", g), g) with
	| (true, Bool(true)) -> eval e1 amb
	| (true, Bool(false)) -> eval e2 amb
	| (_, _) -> failwith ("nonboolean guard"))
| Fun(i, a) -> Closure(i, a, amb)
| Apply(eF, eArg) ->
	let fclosure = eval eF amb in (match fclosure with
	| Closure(arg, fbody, fDecEnv) ->
		let aVal = eval eArg amb in
		let aenv = bind(fDecEnv, arg, aVal) in
		eval fbody aenv
	| RecClosure(f, arg, fbody, fDecEnv) ->
		let aVal = eval eArg amb in
		let rEnv = bind(fDecEnv, f, fclosure) in
		let aenv = bind(rEnv, arg, aVal) in
		eval fbody aenv
	| _ -> failwith("non functional value"))
| Fbin(i1, i2, a) -> ClosureBin(i1, i2, a, amb)
| Applybin(eF, eArg1, eArg2) ->
	let fclosure = eval eF amb in (match fclosure with
	| ClosureBin(arg1, arg2, fbody, fDecEnv) ->
		let aVal1 = eval eArg1 amb in
		let aVal2 = eval eArg2 amb in
		let aenv = bind(fDecEnv, arg1, aVal1) in
		let aenv = bind(aenv, arg2, aVal2) in
		eval fbody aenv
	| RecClosureBin(f, arg1, arg2, fbody, fDecEnv) ->
		let aVal1 = eval eArg1 amb in
		let aVal2 = eval eArg2 amb in
		let rEnv = bind(fDecEnv, f, fclosure) in
		let aenv = bind(rEnv, arg1, aVal1) in
		let aenv = bind(aenv, arg2, aVal2) in
		eval fbody aenv
	| _ -> failwith("non functional value"))
| Diz(xs) -> (match xs with
	|DizVuotoexp -> Dizionario(DizVuoto)
	|List((i,e1),e2) -> if (typecheck("int",(eval e1 amb))) then let tipo = "int" in Dizionario(eval_dizionario xs amb tipo) else if (typecheck("bool",(eval e1 amb))) then let tipo = "bool" in Dizionario(eval_dizionario xs amb tipo) else failwith("not correct element type in dictionary"))
| Search(i,e1) -> (match (eval e1 amb) with
	|Dizionario(e2) -> Bool(has_key(i,e2))
	|_ -> failwith("not a dictionary"))
| Insert(i,e1,e2) -> let diz = (eval e2 amb) in (match diz with 
		|Dizionario(x) -> if has_key(i,x) then failwith("key already exists") else insert(i,(eval e1 amb),diz)
		|_ -> failwith("not a dictionary"))
| Delete(i,e1) -> let diz = (eval e1 amb) in if typecheck("diz",diz) = false then failwith("not a dictionary") else
	(match diz with
		|Dizionario(x) -> if has_key(i,x) = false then failwith("dictionary doesn't contain the key") else Dizionario(remove(i, x))
		|_ -> failwith("not a dictionary"))
| Iterate(f,d) -> let clo = (eval f amb) in
	(match clo with
		|Closure(i,a,en) -> let diz = (eval d amb) in (match diz with
			|Dizionario(x) -> Dizionario(iteration(f,x,amb))
			|_ -> failwith("not a dictionary"))
		|RecClosure(fu, arg, fbody, fDecEnv) -> let diz = (eval d amb) in (match diz with
			|Dizionario(x) -> Dizionario(iteration(f,x,amb))
			|_ -> failwith("not a dictionary"))
		|_ -> failwith("not a function"))
| Fold(f,d) -> let clo = (eval f amb) in
	(match clo with
		|ClosureBin(i1, i2, a, en) -> let diz = (eval d amb) in (match diz with
			|Dizionario(x) -> (match a with
				|Sum(e1,e2) -> folder(f,x,amb,Int(0))
				|Sub(e1,e2) -> folder(f,x,amb,Int(0))
				|Times(e1,e2) -> folder(f,x,amb,Int(1))
				|And(e1,e2) -> folder(f,x,amb,Bool(true))
				|Or(e1,e2) -> folder(f,x,amb,Bool(false))
				|_ -> failwith("unsupported operation"))
			|_ -> failwith("not a dictionary"))
		|RecClosureBin(fu, arg1, arg2, fbody, fDecEnv) -> let diz = (eval d amb) in (match diz with
			|Dizionario(x) -> (match fbody with
				|Sum(e1,e2) -> folder(f,x,amb,Int(0))
				|Sub(e1,e2) -> folder(f,x,amb,Int(0))
				|Times(e1,e2) -> folder(f,x,amb,Int(1))
				|And(e1,e2) -> folder(f,x,amb,Bool(true))
				|Or(e1,e2) -> folder(f,x,amb,Bool(false))
				|_ -> failwith("unsupported operation"))
			|_ -> failwith("not a dictionary"))
		|_ -> failwith("not a function"))
| Filter(lista,d) -> let diz = eval d amb in (match diz with
	|Dizionario(y) -> (match lista with
		|[] -> Dizionario(DizVuoto)
		|x::xs -> Dizionario(filter(lista,y)))
	|_ -> failwith("not a dictionary"))

and eval_dizionario diz amb tipo = match diz with
	|DizVuotoexp -> DizVuoto
	|List((i,e),resto) -> if tipo = "int" then if (typecheck("int",(eval e amb))) then RestoDiz((i, (eval e amb)), (eval_dizionario resto amb tipo)) else failwith("not homogeneous type in dictionary") else if typecheck("bool",(eval e amb)) then RestoDiz((i, (eval e amb)), (eval_dizionario resto amb tipo)) else failwith("not homogeneous type in dictionary")

and iteration(f,diz,amb) = match diz with
	|DizVuoto -> DizVuoto
	|RestoDiz((c,v),z) -> (match v with
		|Int(n) -> let w = CstInt(n) in RestoDiz((c,((eval (Apply(f,w)) amb))),iteration(f,z,amb))
		|Bool(t) -> if t = true then RestoDiz((c,((eval (Apply(f,CstTrue)) amb))),iteration(f,z,amb))
				else RestoDiz((c,((eval (Apply(f,CstFalse)) amb))),iteration(f,z,amb))
		|_ -> failwith("not correct element type in dictionary"))

and folder(f,diz,amb,acc) = match diz with
	|RestoDiz((c,v),z) -> (match v with
		|Int(n) -> let w = CstInt(n) in (match acc with
				|Int(m) -> folder(f,z,amb,(eval (Applybin(f,CstInt(m),w)) amb))
				|Bool(tt) -> if tt = true then folder(f,z,amb,(eval (Applybin(f,CstTrue,w)) amb)) else folder(f,z,amb,(eval (Applybin(f,CstFalse,w)) amb))
				|_ -> failwith("not correct accumulator type"))
		|Bool(t) -> if t = true then (match acc with
				|Int(m) -> folder(f,z,amb,(eval (Applybin(f,CstInt(m),CstTrue)) amb))
				|Bool(tt) -> if tt = true then folder(f,z,amb,(eval (Applybin(f,CstTrue,CstTrue)) amb)) else folder(f,z,amb,(eval (Applybin(f,CstFalse,CstTrue)) amb))
				|_ -> failwith("not correct accumulator type"))
			else (match acc with
				|Int(m) -> folder(f,z,amb,(eval (Applybin(f,CstInt(m),CstFalse)) amb))
				|Bool(tt) -> if tt = true then folder(f,z,amb,(eval (Applybin(f,CstTrue,CstFalse)) amb)) else folder(f,z,amb,(eval (Applybin(f,CstFalse,CstFalse)) amb))
				|_ -> failwith("not correct accumulator type"))
		|_ -> failwith("not correct element type in dictionary"))
	|DizVuoto -> acc;;

let print e = match e with
	|Int(n) -> print_int (n)
	|Bool(t) -> if t = false then print_string ("false") else print_string ("true")
	|_ -> failwith("no correct value");;

let rec print_diz(diz) = match diz with
	|Dizionario(x) -> (match x with
		|RestoDiz((c,v),z) -> (match v with 
			|Int(n) -> print_string(c) ; print_string(": ") ; print_int(n) ; print_string(", ") ; print_diz(Dizionario(z))
			|Bool(t) -> if t = true then (print_string(c) ; print_string(": ") ; print_string("true") ; print_string(", ") ; print_diz(Dizionario(z)))
					else (print_string(c) ; print_string(": ") ; print_string("false") ; print_string(", ") ; print_diz(Dizionario(z)))
			|_ -> failwith("not correct element type in dictionary"))
		|DizVuoto -> print_string("//."))
	|_ -> failwith("not a dictionary");;


print_string("BATTERIA DI TEST:");;
print_newline();;
print_string("1) Creazione dizionario di 4 elementi usando l'espressione apposita:");;
print_newline();;
let d = Diz(List(("i",CstInt(45)),List(("j",CstInt(78)),List(("w",CstInt(50)),List(("z",CstInt(120)),DizVuotoexp)))));;
let dd = eval d (emptyenv(Int(-1)));;
print_diz(dd);;
print_newline();;
let d2 = Let("diz",Diz(DizVuotoexp),Insert("i",CstInt(455),Insert("j",CstInt(788),Insert("w",CstInt(500),Insert("z",CstInt(1200),Den("diz"))))));;
let dd2 = eval d2 (emptyenv(Int(-1)));;
print_string("2) Creazione dizionario di 4 elementi usando l'operazione primitiva Insert:");;
print_newline();;
print_diz(dd2);;
print_newline();;
print_string("3) Creazione dizionario di 2 elementi andando a prendere elementi dall'ambiente locale:");;
print_newline();;
let d3 = Let("diz",Diz(DizVuotoexp),Let("x",CstInt(11),Let("y",CstInt(22),Insert("x",Den("x"),Insert("y",Den("y"),Den("diz"))))));;
let dd3 = eval d3 (emptyenv(Int(-1)));;
print_diz(dd3);;
print_newline();;
print_string("4) Creazione dizionario di 3 elementi che sono il risulato di una funzione:");;
print_newline();;
let d4 = Let("diz",Diz(DizVuotoexp),Let("fun",Fun("p",Or(Den("p"),CstFalse)),Insert("v1",Apply(Den("fun"),CstTrue),Insert("v2",Apply(Den("fun"),CstFalse),Insert("v3",Apply(Den("fun"),CstTrue),Den("diz"))))));;
let dd4 = eval d4 (emptyenv(Int(-1)));;
print_diz(dd4);;
print_newline();;
print_newline();;
print_string("---> Nei 3 test successivi (5-6-7) utilizzerò il primo dizionario {");; print_diz(dd);; print_string("}.");;
print_newline();;
print_newline();;
print_string("5) Cerco la chiave 'z' all'interno del dizionario. Risposta del programma:");;
print_newline();;
let s = Let("diz",Diz(List(("i",CstInt(45)),List(("j",CstInt(78)),List(("w",CstInt(50)),List(("z",CstInt(120)),DizVuotoexp))))),Search("z",Den("diz")));;
let ss = eval s (emptyenv(Int(-1)));;
print(ss);;
print_newline();;
print_string("6) Cerco la chiave 'e' all'interno del dizionario. Risposta del programma:");;
print_newline();;
let s1 = Let("diz",Diz(List(("i",CstInt(45)),List(("j",CstInt(78)),List(("w",CstInt(50)),List(("z",CstInt(120)),DizVuotoexp))))),Search("e",Den("diz")));;
let ss1 = eval s1 (emptyenv(Int(-1)));;
print(ss1);;
print_newline();;
print_string("7) Rimuovo le coppie con chiave 'j' e 'w' dal dizionario:");;
print_newline();;
let r = Let("diz",Diz(List(("i",CstInt(45)),List(("j",CstInt(78)),List(("w",CstInt(50)),List(("z",CstInt(120)),DizVuotoexp))))),Delete("j",Delete("w",Den("diz"))));;
let rr = eval r (emptyenv(Int(-1)));;
print_diz(rr);;
print_newline();;
print_newline();;
print_string("---> Utilizzo il dizionario: {");; print_diz(eval (Diz(List(("i",CstInt(3)),List(("j",CstInt(5)),List(("z",CstInt(4)),DizVuotoexp))))) (emptyenv(Int(-1))));; print_string("}.");;
print_newline();;
print_string("8) Applico la funzione ricorsiva fattoriale a tutti gli elementi del dizionario per mezzo della Iterate:");;
print_newline();;
let i = Let("diz",Diz(List(("i",CstInt(3)),List(("j",CstInt(5)),List(("z",CstInt(4)),DizVuotoexp)))),(Letrec("fact", "n", (Ifthenelse((Eq(Den("n"),CstInt(0))),CstInt(1),(Times(Den("n"),(Apply(Den("fact"),Sub(Den("n"),CstInt(1)))))))),
Iterate(Den("fact"),Den("diz")))));;
let ii = eval i (emptyenv(Int(-1)));;
print_diz(ii);;
print_newline();;
print_string("9) Applico, con lo stesso dizionario, l'operazione Fold che ne fa la somma degli elementi.");;
print_newline();;
let f = Let("diz",Diz(List(("i",CstInt(3)),List(("j",CstInt(5)),List(("z",CstInt(4)),DizVuotoexp)))),(Let("f",Fbin("e","r",Sum(Den("e"),Den("r"))),Fold(Den("f"),Den("diz")))));;
let ff = eval f (emptyenv(Int(-1)));;
print_string("Risposta: ");; print(ff);;
print_newline();;
print_newline();;
print_string("10) Applicazione sequenziale di un And tramite Fold al dizionario: {");; print_diz(eval (Diz(List(("i",CstTrue),List(("j",CstFalse),DizVuotoexp)))) (emptyenv(Int(-1))));; print_string("}.");;
print_newline();;
let f1 = Let("diz",Diz(List(("i",CstTrue),List(("j",CstFalse),DizVuotoexp))),(Let("f",Fbin("e","r",And(Den("e"),Den("r"))),Fold(Den("f"),Den("diz")))));;
let ff1 = eval f1 (emptyenv(Int(-1)));;
print_string("Risposta: ");; print(ff1);;
print_newline();;
print_string("11) Valutazione programma meno semplice che applica il fattoriale con la Iterate e poi fa la somma con Fold degli elementi del dizionario del test 8.");;
print_newline();;
let programma = Let("diz",Diz(List(("i",CstInt(3)),List(("j",CstInt(5)),List(("z",CstInt(4)),DizVuotoexp)))),(Letrec("fact", "n", (Ifthenelse((Eq(Den("n"),CstInt(0))),CstInt(1),(Times(Den("n"),(Apply(Den("fact"),Sub(Den("n"),CstInt(1)))))))),Let("f",Fbin("e","r",Sum(Den("e"),Den("r"))),Fold(Den("f"),Iterate(Den("fact"),Den("diz")))))));;
let prog = eval programma (emptyenv(Int(-1)));;
print_string("Risposta: ");; print(prog);;
print_newline();;
print_string("12) Applico l'operazione Filter al dizionario del test 2 con lista ['z']:");;
print_newline();;
print_string("Dizionario di partenza: {");; print_diz(eval (Let("diz",Diz(DizVuotoexp),Insert("i",CstInt(455),Insert("j",CstInt(788),Insert("w",CstInt(500),Insert("z",CstInt(1200),Den("diz"))))))) (emptyenv(Int(-1))));; print_string("}.");;
print_newline();;
let fil = Let("diz",Diz(DizVuotoexp),Insert("i",CstInt(455),Insert("j",CstInt(788),Insert("w",CstInt(500),Insert("z",CstInt(1200),Filter(["z"],Den("diz")))))));;
let fil = Filter(["z"],Let("diz",Diz(DizVuotoexp),Insert("i",CstInt(455),Insert("j",CstInt(788),Insert("w",CstInt(500),Insert("z",CstInt(1200),Den("diz")))))));;
let fill = eval fil (emptyenv(Int(-1)));;
print_string("Dizionario filtrato: {");; print_diz(fill);; print_string("}.");;
print_newline();;
print_string("13) Svuotamento del dizionario con Filter che riceve lista vuota:");;
print_newline();;
let fil1 = Filter([],Let("diz",Diz(DizVuotoexp),Insert("i",CstInt(455),Insert("j",CstInt(788),Insert("w",CstInt(500),Insert("z",CstInt(1200),Den("diz")))))));;
let fill1 = eval fil1 (emptyenv(Int(-1)));;
print_string("Dizionario di partenza: {");; print_diz(eval (Let("diz",Diz(DizVuotoexp),Insert("i",CstInt(455),Insert("j",CstInt(788),Insert("w",CstInt(500),Insert("z",CstInt(1200),Den("diz"))))))) (emptyenv(Int(-1))));; print_string("}.");;
print_newline();;
print_string("Dizionario filtrato: {");; print_diz(fill1);; print_string("}.");;
print_newline();;


print_newline();;
print_string("LANCIO DI ALCUNE ECCEZIONI:");;
print_newline();;
print_string("1) Tento di inserire un 'true' nel dizionario: {");; print_diz(eval (Diz(List(("i",CstInt(3)),List(("j",CstInt(5)),List(("z",CstInt(4)),DizVuotoexp))))) (emptyenv(Int(-1))));; print_string("}.");;
print_newline();;
let n = Diz(List(("i",CstInt(3)),List(("j",CstInt(5)),List(("z",CstInt(4)),DizVuotoexp))));;
let insn = Insert("tr",CstTrue,n);;
try eval insn (emptyenv(Int(-1))) with e -> print_string(Printexc.to_string e) ; Unbound ;;
print_newline();;
print_string("2) Tento di inserire un elemento con identificatore vuoto:");;
print_newline();;
let n = Diz(List(("i",CstInt(3)),List(("j",CstInt(5)),List(("z",CstInt(4)),DizVuotoexp))));;
let insn = Insert("",CstInt(7),n);;
try eval insn (emptyenv(Int(-1))) with e -> print_string(Printexc.to_string e) ; Unbound ;;
print_newline();;
print_string("3) Tento di creare un dizionario utilizzando l'espressione exp, mettendo tipi di oggetti non omogenei:");;
print_newline();;
let nt = Diz(List(("i",CstInt(45)),List(("j",CstInt(78)),List(("tr",CstTrue),DizVuotoexp))));;
try eval nt (emptyenv(Int(-1))) with e -> print_string(Printexc.to_string e) ; Unbound ;;
print_newline();;
print_string("4) Tento di inserire un elemento con chiave 'i' nel dizionario: {");; print_diz(eval (Diz(List(("i",CstInt(3)),List(("j",CstInt(5)),List(("z",CstInt(4)),DizVuotoexp))))) (emptyenv(Int(-1))));; print_string("}.");;
print_newline();;
let n11 = Diz(List(("i",CstInt(3)),List(("j",CstInt(5)),List(("z",CstInt(4)),DizVuotoexp))));;
let i11 = Insert("i",CstInt(54),n11);;
try eval i11 (emptyenv(Int(-1))) with e -> print_string(Printexc.to_string e) ; Unbound ;;
print_newline();;
print_string("5) Tento di cercare un elemento in un'espressione che non è un dizionario:");;
print_newline();;
let sn = Search("w",Iszero(CstInt(0)));;
try eval sn (emptyenv(Int(-1))) with e -> print_string(Printexc.to_string e) ; Unbound ;;
print_newline();;
print_string("6) Tento di rimuovere l'elemento di chiave 'c' dal dizionario: {");; print_diz(eval (Diz(List(("i",CstInt(3)),List(("j",CstInt(5)),List(("z",CstInt(4)),DizVuotoexp))))) (emptyenv(Int(-1))));; print_string("}.");;
print_newline();;
let na = Diz(List(("i",CstInt(3)),List(("j",CstInt(5)),List(("z",CstInt(4)),DizVuotoexp))));;
let rn = Delete("c",na);;
try eval rn (emptyenv(Int(-1))) with e -> print_string(Printexc.to_string e) ; Unbound ;;
print_newline();;
print_string("7) Tento di applicare la Fold passando come parametro un'espressione che non è una funzione:");;
print_newline();;
let naa = Diz(List(("i",CstInt(3)),List(("j",CstInt(5)),List(("z",CstInt(4)),DizVuotoexp))));;
let fff = Fold(Iszero(CstInt(0)),naa);;
try eval fff (emptyenv(Int(-1))) with e -> print_string(Printexc.to_string e) ; Unbound ;;
print_newline();;
print_string("8) Tento di applicare la Fold con parametro una funzione binaria booleana And al dizionario: {");; print_diz(eval (Diz(List(("i",CstInt(45)),List(("j",CstInt(78)),DizVuotoexp)))) (emptyenv(Int(-1))));; print_string("}.");; print_newline();;
let prerr = Let("diz",Diz(List(("i",CstInt(45)),List(("j",CstInt(78)),DizVuotoexp))),(Let("f",Fbin("e","r",And(Den("e"),Den("r"))),Fold(Den("f"),Den("diz")))));;
try eval prerr (emptyenv(Int(-1))) with e -> print_string(Printexc.to_string e) ; Unbound ;;
print_newline();;


