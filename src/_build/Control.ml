open Printf;;
open Utils;;
open Syntax;;
open Normalize;;
open Semop;;
open Minim;;
open WSemop;;

(*#use "Utils.ml";;
#use "Syntax.ml";;
#use "Normalize.ml";;
#use "Semop.ml";;
#use "Minim.ml";;*)

let help_me = "\n\
Command summary:\n\
  def <name> = <proc>        -> register new definition\n\
  free <proc>                -> free names of process\n\
  bound <proc>               -> bound names of process\n\
  names <proc>               -> names of process\n\
  norm <proc>                -> normalize process\n\
  deriv <proc>               -> show derivatives of process\n\
  lts <proc>                 -> show labelled transition system\n\
  struct <proc> == <proc>    -> check structural congruence\n\
  bisim <proc> ~ <proc>      -> calculate bisimilarity\n\
  bisim ? <proc> ~ <proc>    -> check bisimilarity (slow)\n\
  fbisim ? <proc> ~ <proc>   -> check bisimilarity (fast)\n\
  mini <proc>                -> minimize process\n\
---\n\
  wderiv <proc>              -> show weak derivatives of process\n\
  tderiv <proc>              -> show silent derivatives of processes\n\
  wbisim <proc> ~~ <proc>    -> calculate weak bisimilarities\n\
  wbisim ? <proc> ~~ <proc>  -> check weak bisimilarity (slow)\n\
  wlts <proc>                -> not implemented\n\
  wmini <proc>               -> not implemented\n\
  wfbisim ? <proc> ~~ <proc> -> not implemented\n\
---\n\
  help                       -> this help message\n\
  quit                       -> quit the program\n\
"
let script_mode = ref false ;;

let handle_help () = 
  printf "%s\n> %!" help_me;;

let handle_quit () =
  printf "bye bye !\n%!" ; 
  exit 0;;

let timing operation =
  let start_time = Sys.time()
  in
  let result = operation()
  in
  let end_time = Sys.time()
  in
    (result, end_time -. start_time);; 

(*Lee-Pok*)
let handle_constdef const_name const_val =
  printf "const %s = %d\n%!" const_name const_val;
  Presyntax.const_env := SMap.add const_name (Syntax.Int(const_val)) !Presyntax.const_env;;

let handle_typedef_range type_name min_val max_val =
  let a =
    (try
       (int_of_string min_val)
     with
	 Failure "int_of_string" -> Presyntax.int_of_value(SMap.find min_val !Presyntax.const_env)
    )
  and b =
    (try
       (int_of_string max_val)
     with
	 Failure "int_of_string" -> Presyntax.int_of_value(SMap.find max_val !Presyntax.const_env)
    )
  in
    Presyntax.type_env := SMap.add type_name (Presyntax.PTDefRange(type_name,a,b)) !Presyntax.type_env; 
    printf "type %s = [%d..%d]\n%!" type_name a b;;

let handle_typedef_enum type_name names =
  if !script_mode then
    printf "(handle_typedef_enum %s %s)\n%!" type_name (string_of_list (fun x -> x) names);
  Presyntax.type_env := SMap.add type_name (Presyntax.PTDefEnum(type_name, Utils.set_of_list names)) !Presyntax.type_env;
  printf "type %s = {" type_name;
  printf "%s" (string_of_list (fun x -> x) names);
  printf("}\n");;

let handle_free proc =
  if !script_mode then
    printf "> free %s\n%!" (string_of_process proc);
  printf "%s\n%!" (string_of_set (fun v -> v) (freeNames proc));;

let handle_bound proc =
  if !script_mode then
    printf "> bound %s\n%!" (string_of_process proc);
  printf "%s\n%!" (string_of_set (fun v -> v) (boundNames proc));;

let handle_names proc =
  if !script_mode then
    printf "> names %s\n%!" (string_of_process proc);
  printf "%s\n%!" (string_of_set (fun v -> v) (names proc));;

let handle_normalization proc =
  if !script_mode then
    printf "> norm %s\n%!" (string_of_process proc);
  printf "Normalize process...\n%!";
  let proc', time = timing (fun () -> normalize proc)
  in
    printf "%s\n%!" (string_of_nprocess proc');
    printf "(elapsed time=%fs)\n%!" time;;

let handle_struct_congr p q =
  if !script_mode then
    printf "> struct %s == %s\n%!" (string_of_process p) (string_of_process q);
  printf "Check structural congruence...\n%!";
  let ok, time = timing (fun () -> p === q)
  in
    (if ok then
       printf "the processes *are* structurally congruent\n%!"
     else
       printf "the processes are *not* structurally congruent\n%!");
    printf "(elapsed time=%fs)\n%!" time;; 

let global_definition_map = Hashtbl.create 64;;

let handle_deriv p =
  if !script_mode then
    printf "> deriv %s\n%!" (string_of_process p);
  printf "Compute derivatives...\n%!";
  let op = fun () ->
    let np = normalize p
    in
      derivatives global_definition_map np 
  in
  let derivs, time = timing op
  in
    TSet.iter (fun t -> printf "%s\n" (string_of_derivative t)) derivs;
    printf "(elapsed time=%fs)\n%!" time;; 

let handle_tderiv p =
  if !script_mode then
    printf "> tderiv %s\n%!" (string_of_process p) ;
  printf "Compute silent derivatives...\n%!";
  let op = fun () ->
    let np = normalize p in
      tderivatives global_definition_map np 
  in
  let derivs, time = timing op
  in
    TSet.iter (fun t -> printf "%s\n" (string_of_tderivative t)) derivs;
    printf "(elapsed time=%fs)\n%!" time 
      
let fetch_definition key =
  Hashtbl.find global_definition_map key;;

let register_definition def =
  Hashtbl.replace global_definition_map (string_of_def_header def) def;;

let handle_definition def =
  if !script_mode then
    printf "> %s\n%!" (string_of_definition def);
  register_definition def;
  printf "Definition '%s' registered\n%!" (def_name def);;

let dot_style_format (p, l, p') =
  sprintf "\"%s\" -> \"%s\" [ label = \"%s\", fontcolor=red ]"
    (string_of_nprocess p) (string_of_nprocess p') (string_of_label l);;

let dot_style_format' (pl, l, pl') = 
  sprintf "\"%s\" -> \"%s\" [ label = \"%s\", fontcolor=red ]"
    (string_of_list string_of_nprocess pl)
    (string_of_list string_of_nprocess pl')
    (string_of_label l);;

let handle_lts p =
  if !script_mode then
    printf "> lts %s\n%!" (string_of_process p);
  let transs, time = timing (fun () -> lts global_definition_map (normalize p)) 
  in
    List.iter (fun t -> printf "%s\n" (string_of_transition t)) transs;
    printf "\nGenerating lts.dot... %!";
    let nprocs =
      List.fold_left (fun acc (x, _, y) -> PSet.add x (PSet.add y acc)) PSet.empty transs
    in
    let oc = open_out "lts.dot"
    in
      fprintf oc "digraph LTS {\n";
      PSet.iter
	(fun np -> fprintf oc "\"%s\" [ fontcolor=blue ]\n" (string_of_nprocess np)) nprocs;
      if transs = [] then
	fprintf oc "  0\n"
      else
	List.iter (fun t -> fprintf oc "  %s\n" (dot_style_format t)) transs;
      fprintf oc "}\n";
      close_out oc;
      printf "done\n(elapsed time=%fs)\n%!" time;;

let handle_minimization proc =
  if !script_mode then
    printf "> mini %s\n%!" (string_of_process proc);
  printf "Minimize process...\n%!";
  let transs, time =
    timing
      (fun () -> 
	 let p = normalize proc
	 in
	   minimize global_definition_map p) 
  in
    List.iter (fun t -> printf "%s\n" (string_of_transitions t)) transs;
    printf "\nGenerating lts_mini.dot... %!";
    let nprocs = 
      List.fold_left (fun acc (x, _, y) -> x::(y::acc)) [] transs
    in
    let oc = open_out "lts_mini.dot"
    in
      fprintf oc "digraph LTSMINI {\n";
      List.iter 
	(fun x -> fprintf oc "\"%s\" [ fontcolor=blue ]\n"
	   (string_of_list string_of_nprocess x))
	nprocs;
      if transs = [] then
	fprintf oc "  0\n"
      else
	List.iter (fun t -> fprintf oc "  %s\n" (dot_style_format' t)) transs;
      fprintf oc "}\n";
      close_out oc;
      printf "done\n(elapsed time=%fs)\n%!" time;;

let handle_bisim p1 p2 =
  if !script_mode then
    printf "> bisim %s ~ %s\n%!" (string_of_process p1) (string_of_process p2);
  printf "Calculate bisimilarity...\n%!";
  let start_time = Sys.time()
  in
  let np1 = normalize p1
  in
  let np2 = normalize p2
  in
    try
      let bsm = construct_bisimilarity global_definition_map np1 np2 
      in
      let end_time = Sys.time()
      in
      let print (np1, np2) =
	printf "{ %s ; %s }\n" (string_of_nprocess np1) (string_of_nprocess np2)
      in
	printf "the processes are bisimilar\n(elapsed time=%fs)\n%!" (end_time-.start_time) ;
	BSet.iter print bsm
    with Failure "Not bisimilar" ->
      let end_time = Sys.time()
      in
	printf "the processes are *not* bisimilar\n(elapsed time=%fs)\n%!" (end_time-.start_time);;

let handle_is_bisim p1 p2 =
  if !script_mode then
    printf "> bisim ? %s ~ %s\n%!" (string_of_process p1) (string_of_process p2);
  let ok, time =
    timing
      (fun () -> 
	 let np1 = normalize p1
	 in
	 let np2 = normalize p2
	 in
	   is_bisimilar global_definition_map np1 np2)
  in
    if ok then
      printf "the processes *are* bisimilar\n(elapsed time=%fs)\n%!" time
    else
      printf "the processes are *not* bisimilar\n(elapsed time=%fs)\n%!" time;;

let handle_is_fbisim p1 p2 =
  if !script_mode then
    printf "> fbisim ? %s ~ %s\n%!" (string_of_process p1) (string_of_process p2);
  let ok, time =
    timing
      (fun () ->
	 let np1 = normalize p1
	 in
	 let np2 = normalize p2
	 in
	   is_fbisimilar global_definition_map np1 np2)
  in
    if ok then
      printf "the processes *are* bisimilar\n(elapsed time=%fs)\n%!" time
    else
      printf "the processes are *not* bisimilar\n(elapsed time=%fs)\n%!" time;;

let handle_wbisim p1 p2 =
  if !script_mode then
    printf "> wbisim %s ~ %s\n%!" (string_of_process p1) (string_of_process p2) ;
  printf "Calculate bisimilarity...\n%!";
  let start_time = Sys.time()
  in
  let np1 = normalize p1 in
  let np2 = normalize p2 in
  try
    let bsm = construct_wbisimilarity global_definition_map np1 np2 
    in
    let end_time = Sys.time()
    in
    let print (np1, np2) =
      printf "{ %s ; %s }\n" (string_of_nprocess np1) (string_of_nprocess np2)
    in
      printf "the processes are weak bisimilar\n(elapsed time=%fs)\n%!" (end_time-.start_time) ;
      BSet.iter print bsm
  with Failure "Not weak bisimilar" ->
    let end_time = Sys.time()
    in
      printf "the processes are *not* weak bisimilar\n(elapsed time=%fs)\n%!" (end_time-.start_time);;
	
let handle_is_wbisim p1 p2 =
  if !script_mode then
    printf "> wbisim ? %s ~ %s\n%!" (string_of_process p1) (string_of_process p2) ;
  let ok,time = timing (fun () ->
			  let np1 = normalize p1 in
			  let np2 = normalize p2 in
			    is_wbisimilar global_definition_map np1 np2)
  in
    if ok 
    then printf "the processes *are* weak bisimilar\n(elapsed time=%fs)\n%!" time
    else printf "the processes are *not* weak bisimilar\n(elapsed time=%fs)\n%!" time;;
