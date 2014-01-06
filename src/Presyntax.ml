open Printf;;
open Utils;;
open Syntax;;

type preconstdef =
  | PConstDef of string * int;;

let string_of_preconstdef = function
  | PConstDef (name, value) -> sprintf "const %%%s = %d" name value;;

(* Encodage des valeurs utilisées: booléens, noms symboliques et entiers *)
type prevalue =
  | Bool of bool
  | Name of name
  | Int of int;;

let string_of_prevalue = function
  | Bool b ->
      if b then
	"true"
      else
	"false"
  | Name n -> n
  | Int i -> string_of_int i;;

type pretypedef =
  | PTDefRange of string * int * int
  | PTDefEnum of string * SSet.t;;

let string_of_pretypedef = function
  | PTDefRange(name, min, max) -> sprintf "type %s = [%d..%d]" name min max
  | PTDefEnum(name, names) -> "type " ^ name ^ " = " ^ (string_of_set (fun x -> x) names);;

(*Environnements*)

let const_env : (Syntax.value SMap.t) ref = ref SMap.empty;;
let type_env : (pretypedef SMap.t) ref = ref SMap.empty;;
let var_env : (Syntax.value SMap.t) ref = ref SMap.empty;;

type preexpr =
  | PConst of string
  | PVar of string
  | PParent of preexpr
  | PTrue
  | PFalse
  | PNot of preexpr
  | PAnd of preexpr * preexpr
  | POr of preexpr * preexpr
  | PInt of int
  | PName of string
  | PAdd of preexpr * preexpr
  | PSub of preexpr * preexpr
  | PMul of preexpr * preexpr
  | PDiv of preexpr * preexpr
  | PMod of preexpr * preexpr
  | PInf of preexpr * preexpr
  | PSup of preexpr * preexpr
  | PEq of preexpr * preexpr
  | PNeq of preexpr * preexpr
  | PInfEq of preexpr * preexpr
  | PSupEq of preexpr * preexpr
  | PIf of preexpr * preexpr * preexpr;;
      
let rec string_of_preexpr = function
  | PConst c -> 
    (try Syntax.string_of_value(SMap.find c !const_env)
    with Not_found -> c)
  | PVar v -> 
    (try  sprintf "%s" (string_of_value(SMap.find v !var_env))
     with Not_found -> v)
  | PParent e -> sprintf "[(%s)]" (string_of_preexpr e)
  | PInt n -> string_of_int n
  | PName n -> n
  | PTrue -> "true"
  | PFalse -> "false"
  | PNot e -> sprintf "not(%s)" (string_of_preexpr e)
  | PAnd (e1, e2) -> sprintf "(%s) and (%s)" (string_of_preexpr e1) (string_of_preexpr e2)
  | POr (e1, e2) -> sprintf "(%s) or (%s)" (string_of_preexpr e1) (string_of_preexpr e2)
  | PAdd (e1, e2) -> sprintf "(%s) + (%s)" (string_of_preexpr e1) (string_of_preexpr e2)
  | PSub (e1, e2) -> sprintf "(%s) - (%s)" (string_of_preexpr e1) (string_of_preexpr e2)
  | PMul (e1, e2) -> sprintf "(%s) * (%s)" (string_of_preexpr e1) (string_of_preexpr e2)
  | PDiv (e1, e2) -> sprintf "(%s) / (%s)" (string_of_preexpr e1) (string_of_preexpr e2)
  | PMod (e1, e2) -> sprintf "(%s) %% (%s)" (string_of_preexpr e1) (string_of_preexpr e2)
  | PInf (e1, e2) -> sprintf "(%s) < (%s)" (string_of_preexpr e1) (string_of_preexpr e2)
  | PSup (e1, e2) -> sprintf "(%s) > (%s)" (string_of_preexpr e1) (string_of_preexpr e2)
  | PEq (e1, e2) -> sprintf "(%s) = (%s)" (string_of_preexpr e1) (string_of_preexpr e2)
  | PNeq (e1, e2) -> sprintf "(%s) <> (%s)" (string_of_preexpr e1) (string_of_preexpr e2)  
  | PInfEq (e1, e2) -> sprintf "(%s) <= (%s)" (string_of_preexpr e1) (string_of_preexpr e2)
  | PSupEq (e1, e2) -> sprintf "(%s) >= (%s)" (string_of_preexpr e1) (string_of_preexpr e2)
  | PIf (c, e1, e2) -> sprintf "if (%s) then (%s) else (%s)" (string_of_preexpr c) (string_of_preexpr e1) (string_of_preexpr e2);;

type preprefix =
  | PTau
  | PIn of preexpr (* ? out *)
  | POut of preexpr (* ! sortie *)
  | PReceive of preexpr * string * string
  | PSend of preexpr * preexpr;;

let string_of_preprefix = function
  | PTau -> "tau"
  | PIn n -> sprintf "%s?" (string_of_preexpr n) (* ? out changed *)
  | POut n -> sprintf "%s!" (string_of_preexpr n) (* ! sortie *)
  | PReceive (c, x, t) ->  sprintf "%s?(%s:%s)" (string_of_preexpr c) x t 
  | PSend (c, e) -> sprintf "%s_%s!" (string_of_preexpr c) (string_of_preexpr e);;

let bool_of_value v =
  match v with
    | Syntax.Bool b -> b
    | _ -> failwith "error bool_of_value";;

let int_of_value v =
  match v with
    | Syntax.Int i -> i
    | _ -> failwith "error int_of_value";;

let string_of_value v =
  match v with
    | Syntax.Name n -> n
    | _ -> failwith "error string_of_value";;

(* prend un Preexpr comme argument et renvoie un Syntax.Value *)
let rec value_of_preexpr preexpr =
  match preexpr with
    | PTrue -> Syntax.Bool(true)
    | PFalse -> Syntax.Bool(false)
    | PInt i -> Syntax.Int(i)
    | PName n -> Syntax.Name(n)
    | PConst c -> SMap.find c !const_env
    | PVar v -> SMap.find v !var_env
    | PParent p -> value_of_preexpr p
    | PNot p -> Syntax.Bool(not (bool_of_value (value_of_preexpr p)))
    | PAnd(p1, p2) -> Syntax.Bool(bool_of_value (value_of_preexpr p1) && bool_of_value (value_of_preexpr p2))
    | POr(p1, p2) -> Syntax.Bool(bool_of_value (value_of_preexpr p1) || bool_of_value (value_of_preexpr p2))
    | PAdd(p1, p2) -> Syntax.Int(int_of_value (value_of_preexpr p1) + int_of_value (value_of_preexpr p2))
    | PSub(p1, p2)-> Syntax.Int(int_of_value (value_of_preexpr p1) - int_of_value (value_of_preexpr p2))
    | PMul(p1, p2) -> Syntax.Int(int_of_value (value_of_preexpr p1) * int_of_value (value_of_preexpr p2))
    | PMod(p1, p2) -> Syntax.Int(int_of_value (value_of_preexpr p1) mod int_of_value (value_of_preexpr p2))
    | PDiv(p1, p2) -> Syntax.Int(int_of_value (value_of_preexpr p1) / int_of_value (value_of_preexpr p2))
    | PInf(p1, p2) -> Syntax.Bool(int_of_value (value_of_preexpr p1) < int_of_value (value_of_preexpr p2))
    | PSup(p1, p2) -> Syntax.Bool(int_of_value (value_of_preexpr p1) > int_of_value (value_of_preexpr p2))
    | PInfEq(p1, p2) -> Syntax.Bool(int_of_value (value_of_preexpr p1) <= int_of_value (value_of_preexpr p2))
    | PSupEq(p1, p2) -> Syntax.Bool(int_of_value (value_of_preexpr p1) >= int_of_value (value_of_preexpr p2))
    | PEq(p1, p2) ->
	(match (value_of_preexpr p1), (value_of_preexpr p2) with
	   | Syntax.Bool b1, Syntax.Bool b2 -> Syntax.Bool(b1 = b2)
	   | Syntax.Int i1, Syntax.Int i2 -> Syntax.Bool(i1 = i2)
	   | Syntax.Name n1, Syntax.Name n2 -> Syntax.Bool(n1 = n2)
	   | _ -> failwith "compare error")
    | PNeq(p1, p2) ->
	(match (value_of_preexpr p1), (value_of_preexpr p2) with
	   | Syntax.Bool b1, Syntax.Bool b2 -> Syntax.Bool(not(b1 = b2))
	   | Syntax.Int i1, Syntax.Int i2 -> Syntax.Bool(not(i1 = i2))
	   | Syntax.Name n1, Syntax.Name n2 -> Syntax.Bool(not(n1 = n2))
	   | _ -> failwith "compare error")
    | PIf(p1, p2, p3)-> 
	(match bool_of_value (value_of_preexpr p1) with
	   | true -> value_of_preexpr p2 
	   | false -> value_of_preexpr p3);;

let rec valuelist_of_preexprlist preexprlist =
  match preexprlist with
    | [] -> []
    | head::tail -> (value_of_preexpr head)::valuelist_of_preexprlist tail;;

type preprocess =
  | PSilent
  | PPrefix of preprefix * preprocess
  | PSum of preprocess * preprocess
  | PPar of preprocess * preprocess
  | PRes of Syntax.name * preprocess
  | PCall of string * preexpr list
  | PRename of Syntax.name * Syntax.name * preprocess
  | PGuard of preexpr * preprocess;;

let rec string_of_preprocess = function

  | PSilent -> "0"
  | PPrefix(a, p) ->
      let st = string_of_preprefix a in
	sprintf "%s,%s" st (string_of_preprocess p)
  | PSum(p, q) -> sprintf "(%s+%s)" (string_of_preprocess p) (string_of_preprocess q)
  | PPar(p, q) -> sprintf "(%s||%s)" (string_of_preprocess p) (string_of_preprocess q)
  | PRes(n, p) -> sprintf "new(%s)[%s]" n (string_of_preprocess p)
  | PCall(d, es) -> d ^ (string_of_args string_of_preexpr es)
  | PRename(old, value, p) -> sprintf "(%s)[%s/%s]" (string_of_preprocess p)  value old
  | PGuard(g, p) -> 
    sprintf "when (%s) %s" (string_of_preexpr g) (string_of_preprocess p);;

(* transformer un preprefixe en prefixe  *)
let prefix_of_preprefix preprefix =
  printf "Transforming prefix:\n%s\n%!" (string_of_preprefix preprefix);
  match preprefix with
    | PTau -> Tau
    | PIn(PName n) -> In(n) 
    | POut(PName n) -> Out(n)
    | PReceive(PName n, var, _) -> 
     ( try In(n ^ "_" ^ (string_of_value (SMap.find var !var_env)))
      with Not_found -> failwith "ùdsk,dl"
     )
    | PSend(PName n, preexpr) -> Out(n ^ "_" ^ (string_of_preexpr preexpr))
    | _ -> failwith "error canal name";;

(* construire une liste de Syntax.Int *)
let rec build_syntax_list a b =
  if(a > b)then
    []
  else
    (Syntax.Int a)::(build_syntax_list (a + 1) b);;


(* construire la liste du type typ
   ex: type Range=[0..2]  -> [Syntax.Int(0);Syntax.Int(1);Syntax.Int(2)] *)
let get_type_values typ =
  match (SMap.find typ !type_env) with
    | PTDefRange(_, min, max) -> build_syntax_list min max
    | PTDefEnum(_, names) -> 
	let list_of_set lset = 
	  let conc hd tl = (Syntax.Name hd) :: tl in 
	    SSet.fold conc lset [] in
	  list_of_set names;;      

(*  *)
let rec sum_processes process_list =
  match process_list with
    | [] -> failwith "empty"
    | [e] -> e
    | head::tail -> PSum(head, sum_processes tail);;

let process_of_receive exp var value preprocess =
match value with
  |Syntax.Int i->
    var_env := SMap.add var value !var_env;
    PPrefix( PIn
	       (PName (
		 (string_of_preexpr exp)^ "_" ^ (string_of_int i))
	       )
	       , preprocess)  
  |Syntax.Name n ->  
    var_env := SMap.add var value !var_env;
    PPrefix( PIn
	       (PName (
		 (string_of_preexpr exp)^ "_" ^ n)
	       )
	       , preprocess)  
  |_ -> failwith "*.*";;

let rec list_process_of_receive exp var valueList p =
  match valueList with
    | [] -> []
    | head::tail -> (process_of_receive exp var head p)::list_process_of_receive exp var tail p;;

let rec process_of_preprocess preprocess =
 printf "Transforming process:\n%s\n%!" (string_of_preprocess preprocess);
  match preprocess with
    | PSilent -> Silent
    | PPrefix(a, p) -> 
	(match a with
	   | PReceive(exp, var, type_range) -> 
	     process_of_preprocess(
	       sum_processes (
		 (List.rev (list_process_of_receive exp var (get_type_values type_range) p))
	       ))
	   | _ as prepref -> Prefix(prefix_of_preprefix prepref, process_of_preprocess p))
    | PSum(p, q) -> Sum(process_of_preprocess p, process_of_preprocess q)
    | PPar(p, q) -> Par(process_of_preprocess p, process_of_preprocess q)
    | PRes(n, p) -> Res(n, process_of_preprocess p)
    | PCall(d, es) -> Call(d, valuelist_of_preexprlist es)
    | PRename(old, value, p) -> Rename(old, value, process_of_preprocess p)
    | PGuard(cond, p) -> 
	(match (value_of_preexpr cond) with
	  | Syntax.Bool(true) -> (process_of_preprocess p)
	  | Syntax.Bool(false) -> Silent
	  | _ -> failwith("Guard must be a boolean (process_of_preprocess)")
	);;

type preparam =
  | PParamVar of string * string
  | PParamBool of bool
  | PParamName of name
  | PParamInt of int;;

let string_of_preparam preparam =
  match preparam with
    | PParamVar (x, t) -> sprintf "%s:%s" x t
    | PParamBool b ->
	if b then
	  "true"
	else
	  "false"
    | PParamName n -> n
    | PParamInt n -> string_of_int n;;

type predefinition = PDefinition of string * preparam list * preprocess;;

let string_of_predef_header (PDefinition (name, params, _)) = 
  name^(string_of_args string_of_preparam params);;

let string_of_predefinition = function
  | PDefinition (_, _, body) as def ->
      "def " ^ (string_of_predef_header def) ^ " = " ^ (string_of_preprocess body);;

let rec value_of_preparam preparamlist =
  match preparamlist with
    | [] -> []
    | head::tail ->
	(match head with
	   | PParamVar(s1, s2) -> Syntax.Name(s1 ^ s2)::value_of_preparam tail  
	   | PParamBool b -> Syntax.Bool(b)::value_of_preparam tail
	   | PParamName(n) -> Syntax.Name(n)::value_of_preparam tail
	   | PParamInt(i) -> Syntax.Int(i)::value_of_preparam tail);;

let definitions_of_predefinition predefinition =
  let a =
  match predefinition with
    | PDefinition(s, ppmlist, preprocess) -> [Syntax.Definition(s, value_of_preparam ppmlist, process_of_preprocess preprocess)]
  in 
printf "Transforming definition:\n%s\n%!" (string_of_predefinition predefinition); a;;
