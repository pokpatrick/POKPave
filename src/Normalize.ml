open Printf;;
open Utils;;
open Syntax;;

(*#use "Utils.ml";;
  #use "Syntax.ml";;*)

(**************************************************)
(**** Algorithme optimise de normalisation     ****)
(**** des processus et application a la        ****)
(**** congruence structurelle                  ****)
(**************************************************)

(** Algorithme essentiellement imagine par B.Vaugon **)

(* Structure inductive de la syntaxe des processus CCS normalisés *)
type nproc =
  | NSilent
  | NPrefix of prefix * nproc
  | NSum of nproc list
  | NPar of nproc list
  | NCall of string * value list
  | NRename of name * name * nproc;;

type nprocess = SSet.t * nproc;;

let string_of_nprocess (res, nproc) =
  let rec string_of_nproc = function
    | NSilent -> "0"
    | NPrefix(a, p) -> sprintf "%s, %s" (string_of_prefix a) (string_of_nproc p)
    | NSum(ps) -> string_of_collection "(" ")" "+" string_of_nproc ps
    | NPar(ps) -> string_of_collection "(" ")" "||" string_of_nproc ps
    | NCall(d, vs) -> d ^ (string_of_args string_of_value vs)
    | NRename (var, name, p) -> sprintf "(%s)[%s/%s]" (string_of_nproc p) name var
  in
    if SSet.is_empty res then
      string_of_nproc nproc
    else
      "new" ^ (string_of_args (fun x -> x) (SSet.elements res)) ^ "[" ^
	(string_of_nproc nproc) ^ "]";;

let is_normalized (_, nproc, _) =
  let rec norm = function
    | NPrefix (_, q) -> norm q
    | NSum ps ->
	List.for_all (fun p ->
			match p with
			  | NSum _ -> false
			  | _ -> norm p) ps
    | NPar ps ->
	List.for_all (fun p ->
			match p with
			  | NPar _ -> false
			  | _ -> norm p) ps
    | NSilent | NCall (_, _) -> true
    | NRename (_, _,q) -> norm q
  in
    norm nproc;;

(* nfreeNames: nproc -> SSet.t *)
let rec nfreeNames = function
  | NSilent | NCall (_, _) -> SSet.empty
  | NPrefix (Tau, np) -> nfreeNames np
  | NPrefix (In name, np) | NPrefix (Out name, np) ->
      SSet.add name (nfreeNames np)
  | NSum nps | NPar nps ->
      List.fold_left (fun acc np -> SSet.union (nfreeNames np) acc)
	SSet.empty nps
  | NRename(var,name,p) -> SSet.add name (SSet.add var (nfreeNames p));;

let simplify (res, nproc) =
  let rec simplify_ps cons ps =
    let simplify_one ps' p =
      let p' = sub_simplify p
      in
	match p' with
	  | NSilent -> ps'
	  | NSum l ->
	      (match cons [] with
		 | NSum _ -> l @ ps'
		 | _ -> p' :: ps')
	  | NPar l ->
	      (match cons [] with
		 | NSum _ -> l @ ps'
		 | _ -> p' :: ps')
	  | _ -> p' :: ps'
    in
      match List.fold_left simplify_one [] ps with
	| [] -> NSilent
	| [p] -> p
	| ps' -> cons ps'
  and sub_simplify np =
    match np with
      | NSilent | NCall (_, _) -> np
      | NPrefix (a, p) -> NPrefix (a, sub_simplify p)
      | NSum ps -> simplify_ps (fun ps' -> NSum ps') ps
      | NPar ps -> simplify_ps (fun ps' -> NPar ps') ps
      | NRename (var, name, p) -> NRename (var, name, sub_simplify p)
  in
    (res, sub_simplify nproc);;

let denormalize (res, nproc) =
  let rec denorm_sub = function
    | NSilent -> Silent
    | NPrefix(a, p) -> Prefix (a, denorm_sub p)
    | NSum(ps) ->
	List.fold_right (fun p q -> Sum(p, q)) (List.map denorm_sub ps) Silent
    | NPar(ps) ->
	List.fold_right (fun p q -> Par(p, q)) (List.map denorm_sub ps) Silent
    | NCall(d, vs) -> Call(d, vs)
    | NRename(var, name, p) -> Rename (var, name, denorm_sub p)
  in
    SSet.fold (fun n p -> Res (n, p)) res (denorm_sub nproc);;

(***)
let rec mem_target a list = 
  match list with
    | [] -> false
    | (target, _)::tl ->
	if (target = a) then
	  true
	else
	  mem_target a tl;;

let mem_value a list = 
  match list with
    | [] -> false 
    | (_, value)::tl ->
	if (value = a) then
	  true
	else
	  mem_target a tl;;

let simple_normalize proc =
  let frees = freeNames proc
  in
  let init_map = SSet.fold (fun n -> SMap.add n n) frees SMap.empty
  in
  let counter = ref 0
  in
  let nus = ref SSet.empty
  in
  let init_map' = ref init_map
  in
  let rec gen () =
    let var = "f" ^ (string_of_int !counter)
    in
      incr counter;
      if SSet.mem var frees || SSet.mem var !nus then
	gen ()
      else
	( nus := SSet.add var !nus ; var )
  in
  let rec snorm_one map = function
    | Silent -> Silent
    | Prefix (Tau, proc) -> Prefix (Tau, snorm_one map proc)
    | Prefix (In name, proc) -> Prefix (In (SMap.find name map), snorm_one map proc)
    | Prefix (Out name, proc) -> Prefix (Out (SMap.find name map), snorm_one map proc)
    | Sum (proc1, proc2) ->  Sum(snorm_one map proc1, snorm_one map proc2)
    | Par (proc1, proc2) -> Par(snorm_one map proc1, snorm_one map proc2)
    | Res (name, proc) -> 
	let fname = gen()
	in
	let map' = SMap.add name fname map
	in
          init_map' := SMap.add name fname map;
          snorm_one map' proc
    | Call (name, args) -> Call (name, args)
    | Rename (old,value,proc) ->
	let value' =
          if SMap.mem value map then
	    SMap.find value map
          else
	    value
	in
          Rename(old,value', snorm_one map proc)
  in
  let tmpproc =
    snorm_one init_map proc 
  in
  let findname name map =
    if SSet.mem name !nus then 
      name
    else
      SMap.find name map
  in
  let rec norm_sub map = function 
    | Silent -> NSilent
    | Prefix (Tau, proc) -> NPrefix (Tau, norm_sub map proc)
    | Prefix (In name, proc) -> NPrefix (In (findname name map), norm_sub map proc)
    | Prefix (Out name, proc) -> NPrefix (Out (findname name map), norm_sub map proc)
    | Sum (proc1, proc2) ->
	begin match (norm_sub map proc1, norm_sub map proc2) with
	  | (NSum sub1, NSum sub2) -> NSum (sub1 @ sub2)
	  | (NSum sub1, nproc2) -> NSum (nproc2 :: sub1)
	  | (nproc1, NSum sub2) -> NSum (nproc1 :: sub2)
	  | (nproc1, nproc2) -> NSum [ nproc1 ; nproc2 ]
	end
    | Par (proc1, proc2) ->
	begin match (norm_sub map proc1, norm_sub map proc2) with
	  | (NPar sub1, NPar sub2) -> NPar (sub1 @ sub2)
	  | (NPar sub1, nproc2) -> NPar (nproc2 :: sub1)
	  | (nproc1, NPar sub2) -> NPar (nproc1 :: sub2)
	  | (nproc1, nproc2) -> NPar [ nproc1 ; nproc2 ]
	end
    | Res (_, proc) -> norm_sub map proc
    | Call (name, args) -> NCall (name, args)
    | Rename (old,value,proc) ->
	let value' = 
          if SMap.mem value map then
	    findname value map
          else
	    value
	in
	  NRename (old, value', norm_sub map proc)
  in
  let nproc = norm_sub init_map tmpproc
  in
  let nproc_frees = freeNames (denormalize (SSet.empty, nproc))
  in
  let nus = SSet.inter !nus nproc_frees
  in
    ((nus, nproc), frees);;

let complex_normalize ((bounded : SSet.t), nproc) frees =
  let (bnd1, bnd2) =
    let rec create s n =
      let name = s ^ (string_of_int n)
      in
	if SSet.mem name frees then create s (succ n) else name
    in
      (create "x" 0, create "y" 0)
  in
  let rec norm nproc =
    match nproc with
      | NSilent | NCall (_, _) -> nproc
      | NPrefix (pref, nproc) -> NPrefix (pref, norm nproc)
      | NSum nprocs -> NSum (List.sort compare (List.map norm nprocs))
      | NPar nprocs -> NPar (List.sort compare (List.map norm nprocs))
      | NRename (var,name,nproc) -> NRename (var,name,norm nproc)
  in
  let abstract_bounded bnd =
    let prefix_img name =
      if name = bnd then
	bnd1
      else
	if SSet.mem name frees then
	  name
	else
	  bnd2
    in
    let rec f np =
      match np with
	| NSilent | NCall (_, _) -> np
	| NPrefix (Tau, np) -> NPrefix (Tau, f np)
	| NPrefix (In name, np) -> NPrefix (In (prefix_img name), f np)
	| NPrefix (Out name, np) -> NPrefix (Out (prefix_img name), f np)
	| NSum nps -> NSum (List.map f nps)
	| NPar nps -> NPar (List.map f nps)
        | NRename (var,name,np) -> NRename (prefix_img var, prefix_img name, f np)
    in
      (norm (f nproc), bnd)
  in
  let (name_map, new_bounded) =
    let free_map = SSet.fold (fun x -> SMap.add x x) frees SMap.empty
    in
    let rec add_bounded apl cnt ((map, bnds) as acc) =
      match apl with
	| [] -> acc
	| (_, b) :: tl ->
	    let name = "f" ^ (string_of_int cnt)
	    in
	      if SMap.mem name free_map then
		add_bounded apl (succ cnt) acc
	      else
		add_bounded tl (succ cnt) (SMap.add b name map, SSet.add name bnds)
    in
    let comp (x, _) (y, _) = compare x y
    in
    let abstract_procs = List.map abstract_bounded (SSet.elements bounded)
    in
    let sorted_aprocs = List.sort comp abstract_procs
    in
      add_bounded sorted_aprocs 0 (free_map, SSet.empty)
  in
  let rec rename np =
    match np with
      | NSilent | NCall (_, _) -> np
      | NPrefix (Tau, np) -> NPrefix (Tau, rename np)
      | NPrefix (In name, np) -> NPrefix (In (SMap.find name name_map), rename np)
      | NPrefix (Out name, np) -> NPrefix (Out (SMap.find name name_map), rename np)
      | NSum nps -> NSum (List.map rename nps)
      | NPar nps -> NPar (List.map rename nps)
      | NRename(var,name,np) -> 
          let name' = 
            if SMap.mem name name_map then
	      SMap.find name name_map
            else
	      name
          in
            NRename(var,name',rename np)
  in
    (new_bounded, norm (rename nproc));;

let normalize proc =
  let (nproc, frees) = simple_normalize proc
  in
  let nproc' = simplify nproc
  in
  let nproc'' = complex_normalize nproc' frees
  in
    nproc'';;

let renormalize nprocess =
  let (res', nproc') = simplify nprocess
  in
  let internals = nfreeNames nproc'
  in
  let frees = SSet.diff internals res'
  in
  let res = SSet.inter res' internals
  in
    complex_normalize (res, nproc') frees;;

(***)

let nproc_subst nproc m n =
  let rename x =
    if x = m then
      n
    else
      x in
  let rec f np =
    match np with
      | NSilent | NCall (_, _) -> np
      | NPrefix (Tau, np) -> NPrefix (Tau, f np)
      | NPrefix (In x, np) -> NPrefix (In (rename x), np)
      | NPrefix (Out x, np) -> NPrefix (Out (rename x), np)
      | NSum nps -> NSum (List.map f nps)
      | NPar nps -> NPar (List.map f nps)
      | NRename (var,name,np) -> NRename (rename var, rename name, np)
  in
    f nproc;;

let nsubst (res, nproc) m n =
  (SSet.add n (SSet.remove m res), nproc_subst nproc m n);;

let rec nsubsts p ms ns = match (ms,ns) with
  | ([], []) -> p
  | ([], _) -> failwith "nsubsts: bad cosupport"
  | (_, []) -> failwith "nsubsts: bad support"
  | (m::ms',n::ns') -> nsubsts (nsubst p m n) ms' ns';;

let struct_congr p q =
  (normalize p) = (normalize q);;

let (===) = struct_congr;;
