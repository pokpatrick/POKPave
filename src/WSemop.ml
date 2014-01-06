open Printf

open Utils
open Normalize
open Semop

let string_of_tderivative (_,_,p') =
  sprintf "--[%s*]-> %s" tau_str (string_of_nprocess p')

let remove_dupl_derivs derivs_to_test =
   let test_if_dupl ((_, lab, np) as trans) derivs =
     let equal_derivs (_, lab2, np2) other_result =
       let result = Pervasives.compare (lab, np) (lab2, np2) in
       other_result || result = 0 in
     if (TSet.fold equal_derivs derivs false) then derivs
     else TSet.add trans derivs in
   TSet.fold test_if_dupl derivs_to_test TSet.empty;;

let tderivatives defs orig_nproc =
  let rec tderivatives_sub defs_s pre_derivs old_derivs = 
      let filter (_, lab, _) =
	match lab with
	  | T_Tau -> true
	  | _ -> false
      in
      let join_next_derivs (_, _, np) prec_derivs = 
	let cur_derivs =  derivatives defs_s np in 
	let all_tau_derivs = TSet.filter filter cur_derivs in
	let tau_derivs = remove_dupl_derivs all_tau_derivs in
	TSet.union prec_derivs tau_derivs in
      let next_derivs = TSet.fold join_next_derivs pre_derivs TSet.empty in
      let new_old_derivs = TSet.union old_derivs pre_derivs in
      if TSet.subset next_derivs new_old_derivs then 
	new_old_derivs
      else
	tderivatives_sub defs_s next_derivs new_old_derivs in
  let init_derivs = TSet.singleton (orig_nproc, T_Tau, orig_nproc) in
  TSet.remove (orig_nproc, T_Tau, orig_nproc) (tderivatives_sub defs init_derivs TSet.empty);;

let wderivatives defs orig_nproc = 
  let init_tderivs = 
    TSet.add (orig_nproc, T_Tau, orig_nproc) (tderivatives defs orig_nproc) in
  let filter (_, lab, _) =
      match lab with
	| T_Tau -> false
	| _ -> true
  in
  let join_derivs (_, _, np) prec_derivs = 
    let new_derivs = TSet.filter filter (derivatives defs np) in 
    TSet.union prec_derivs new_derivs in
  let init_wderivs =  TSet.fold join_derivs init_tderivs TSet.empty in
  let join_wderivs ((s_np, lab, np) as wderiv) prec_derivs =
    let new_tderivs = tderivatives defs np in
    let convert_to_wderiv (_, _, t_np) =
      (s_np, lab, t_np) in
    let convert_to_wderiv_and_join ((_, _, t_np) as tderiv) prec_wderivs =
      let snd_derivs = derivatives defs t_np in
      let has_strong_snd_derivs = (TSet.is_empty snd_derivs) || not 
	(TSet.is_empty (TSet.filter filter snd_derivs)) in
      if has_strong_snd_derivs 
      then TSet.add (convert_to_wderiv tderiv) prec_wderivs 
      else prec_wderivs in
    let new_wderivs =
      (TSet.fold convert_to_wderiv_and_join (TSet.add wderiv new_tderivs) TSet.empty) in
    TSet.union new_wderivs prec_derivs in
  remove_dupl_derivs (TSet.fold join_wderivs init_wderivs TSet.empty)
;;

let wlts defs p =
   let rec f acc_trans procs_todo procs_done =
    try
      let p = PSet.choose procs_todo in
      let derivs = wderivatives defs p in
      let new_acc_trans = TSet.union acc_trans derivs in
      let next_procs =
	TSet.fold (fun (_,_,dst) acc -> PSet.add dst acc) derivs PSet.empty
      in
      let new_procs_todo =
	PSet.remove p (PSet.union (PSet.diff next_procs procs_done) procs_todo)
      in
      let new_procs_done = PSet.add p procs_done in
	f new_acc_trans new_procs_todo new_procs_done
    with Not_found -> acc_trans
  in
  let transs = f TSet.empty (PSet.singleton p) PSet.empty in
    TSet.fold (fun t acc -> t :: acc) transs [];;

let construct_wbisimilarity defs nproc1 nproc2 =
  let rec construct bsm np1 np2 =
    let d1s = derivatives defs np1 in
    let td1s = tderivatives defs np1 in
    let wd1s = wderivatives defs np1 in
    let d2s = derivatives defs np2 in
    let wd2s = wderivatives defs np2 in
    let td2s = tderivatives defs np2 in
    let folder wdys tdys inv (_, labx, dstx) acc_bsm =
      let build found_nproc derivs search = 
	let dst1 = if inv then found_nproc else dstx in
	let dst2 = if inv then dstx else found_nproc in
	let dsts = (dst1, dst2) in
	if BSet.mem dsts acc_bsm || BSet.mem (dst2, dst1) acc_bsm
	  || dst1 = dst2 then acc_bsm
	else
	  try construct (BSet.add dsts acc_bsm) dst1 dst2
	  with Failure "Bad path" -> 
	    if TSet.is_empty derivs then failwith "Bad path" 
	    else search derivs in
      let rec tsearch acc_tdys =	
	let (found_np, new_tderivs) =
	  if TSet.is_empty acc_tdys then 
	    let np = if inv then np1 else np2 in
	    (np, TSet.empty)
	  else 
	    let ((_, _, tdsty) as tty) = TSet.choose acc_tdys in
	    (tdsty, TSet.remove tty acc_tdys) in
	build found_np new_tderivs tsearch in
      let rec wsearch acc_wdys =	
	if (TSet.is_empty acc_wdys) then failwith "Bad path"
	else
	  let ((_, wlaby, wdsty) as wty) = TSet.choose acc_wdys in	  	      
	  if labx <> wlaby then wsearch (TSet.remove wty acc_wdys)
	  else
	    build wdsty (TSet.remove wty acc_wdys) wsearch in		  
      match labx with
	    | T_Tau -> tsearch tdys	    
	    | _ -> wsearch wdys
    in
    TSet.fold (folder wd2s td2s false) d1s
      (TSet.fold (folder wd1s td1s true) d2s bsm)
  in
  try construct (BSet.singleton (nproc1, nproc2)) nproc1 nproc2
  with Failure "Bad path" -> failwith "Not weak bisimilar";;

let is_wbisimilar defs nproc1 nproc2 = 
  try ignore (construct_wbisimilarity defs nproc1 nproc2) ; true
  with Failure "Not weak bisimilar" -> false;;

