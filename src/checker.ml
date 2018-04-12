open Util
open Expr 
open State

module C = Shrcnt

let cnp n p =
  let rec aux n p m d =
    if n = 1 then Z.div (Z.mul (Z.of_int p) m) d
    else aux (n-1) (p-1) (Z.mul (Z.of_int p) m) (Z.mul (Z.of_int n) d) in
  if n = 0 then Z.one 
  else aux n p Z.one Z.one

module L : sig

  type ldf = {
      n : int;    (* number of elements to take in l *)
      l : (expr * expr) list;
      p : int;    (* size of l *)
      cnp: Z.t;   (* cnp n p *)
      c : Z.t;    (* total number of tuple to check *)
    }

  type ldfs = ldf list

  val cons : int -> (expr * expr) list -> int -> ldfs -> ldfs

  val cnp_ldfs : ldfs -> Z.t
  val lfirst : ldfs -> (expr * expr) list
  val set_top_exprs : state -> (expr * expr) list -> unit
  val set_top_exprs2 : state -> ldfs -> unit

  val simplify_ldfs : state -> int -> ldfs -> bool * ldfs

  val rev_append : ldfs -> ldfs -> ldfs

end = struct
  type ldf = {
      n : int;    (* number of elements to take in l *)
      l : (expr * expr) list;
      p : int;    (* size of l *)
      cnp: Z.t;   (* cnp n p *)
      c : Z.t;    (* total number of tuple to check *)
    }

  type ldfs = ldf list

  let cnp_ldfs = function
    | []       -> Z.one
    | ldf :: _ -> ldf.c
    
  let cons n l p tl = 
    let cnp = cnp n p in
    { n; l; p; cnp; c = Z.mul cnp (cnp_ldfs tl)} ::  tl

  let lfirst ldfs = 
    let rec first n hd tl = 
      if n = 0 then hd 
      else match tl with
           | x::tl -> first (n-1) (x::hd) tl
           | []   -> assert false in
    let rec aux hd ldfs = 
      match ldfs with
      | [] -> hd
      | { n = d; l = fs} ::ldfs -> aux (first d hd fs) ldfs in
    aux [] ldfs

  let set_top_exprs state es = 
    List.iter (fun (e,_) -> ignore (add_top_expr state e)) es

  let set_top_exprs2 state ldfs = 
    List.iter (fun ldf -> set_top_exprs state ldf.l) ldfs

  let simplify_ldfs state maxparams ldfs = 
    clear_state state;
    set_top_exprs2 state ldfs;
    init_todo state;
    let res = simplify_until state maxparams in
    if res then (* Not need to do more work just return *)
      false, ldfs
    else 
      let simple = simplified_expr state in
      true, List.map (fun ldf -> 
                {ldf with l =  List.map (fun (e1, e2) -> simple e1, e2) ldf.l }) ldfs

  let rec rev_append l1 l2 = 
    match l1 with
    | [] -> l2
    | ldf::l1 -> rev_append l1 ({ ldf with c = Z.mul ldf.cnp (cnp_ldfs l2) }::l2)
  
end

exception CanNotCheck of (expr * expr) list 
  
let print_error fmt lhd = 
  Format.fprintf fmt "@[<v>Cannot check@ %a@ reduce to@ %a@]"
    (pp_list ",@ " (fun fmt (_,e2) -> pp_expr fmt e2)) lhd
    (pp_list ",@ " (fun fmt (e1,_) -> pp_expr fmt e1)) lhd


let find_bij state maxparams ldfs =
  let lhd = L.lfirst ldfs in
  clear_state state;
  L.set_top_exprs state lhd;
  init_todo state;
  if not (simplify_until state maxparams) then 
    let simple = simplified_expr state in
    let lhd = List.map (fun (e1,e2) -> simple e1, e2) lhd in
    raise (CanNotCheck lhd)
  else
    let used_share = used_share state in
    L.set_top_exprs2 state ldfs;
    clear_bijection state;    
    init_todo state;
    simplify_until_with_clear state used_share maxparams;
    let is_in (e1, _) = is_top_expr state e1 in
    List.map (fun ldf -> List.partition is_in ldf.L.l) ldfs 

(*
exception Found_ee of (expr * expr)

let rec can_remove ldfs =
  match ldfs with
  | [] -> [] 
  | ldf :: ldfs ->
    let cr = can_remove ldfs in
    if ldf.L.n < ldf.L.p then (ldf.L.n, ldf.L.l, ldf.L.p) :: cr
    else cr

let find_bij state maxparams ldfs =
  clear_state state;
  L.set_top_exprs2 state ldfs;
  init_todo state;
  let _ = 
    try simplify_until_with_clear2 state maxparams (can_remove ldfs)
    with State.CanNotCheck le ->
      let find e =
        try 
          List.iter (fun ldf ->
              List.iter (fun (e1,e2) -> 
                  if E.equal e e1 then 
                    raise (Found_ee(e1,e2))) ldf.L.l) ldfs;
          assert false
        with Found_ee ee -> ee in
      raise (CanNotCheck (List.map find le))
  in
  let is_in (e1, _) = is_top_expr state e1 in
  List.map (fun ldf -> List.partition is_in ldf.L.l) ldfs
 
 *)
let pp_z fmt z = 
  let s = Z.to_string z in
  let len = Bytes.length s in
  let s' = 
    let m = len mod 3 in
    if m = 0 then ""
    else Bytes.make (3 - m) '0' in

  let s = s' ^ s in
  let k = Bytes.length s / 3 in
  for i = 0 to k - 1 do
    for j = 0 to 2 do
      Format.fprintf fmt "%c" s.[i*3 + j]
    done;
    if i <> k-1 then Format.fprintf fmt "," 
  done

let pp_human suffix fmt num =
  let sfx = [| ""; "K"; "M"; "G"; "T"; "P"; "E"; "Z"; "Y" |] in
  let idx = ref 0 in
  let num = ref num in
  let fcr = ref None in

  while !idx < (Array.length sfx - 1) && Z.gt !num (Z.of_int 1000) do
    fcr := Some (Z.rem !num (Z.of_int 1000));
    num := Z.div !num (Z.of_int 1000);
    idx := !idx + 1
  done;
  let suffix = sfx.(!idx) ^ suffix in

  match !fcr with
  | None ->
      Format.fprintf fmt "%s %s" (Z.to_string !num) suffix
  | Some fcr ->
      Format.fprintf fmt "%s.%0.3d %s"
        (Z.to_string !num) (Z.to_int fcr) suffix
      
  
let check_all state maxparams (ldfs:L.ldfs) = 
  let to_check = L.cnp_ldfs ldfs in
  Format.eprintf "%a tuples to check@." pp_z to_check;
  let tdone = ref Z.zero in
  let count = ref 0 in
  let t0 = Sys.time () in
  let rec check_all state maxparams (ldfs:L.ldfs) = 
    incr count;    
    if !count land 0x3FFFF = 0 then 
      Format.eprintf "%a tuples checked over %a in %.3f@."
        pp_z !tdone pp_z to_check (Sys.time () -. t0);

(*    let pp_ldf fmt ldf = 
      Format.fprintf fmt "[%i : %a]" ldf.L.n 
          (Util.pp_list ", " (fun fmt (e1,_e2) -> pp_expr fmt e1)) ldf.L.l in
    Format.eprintf "check_all %a@." 
               (Util.pp_list " " pp_ldf) ldfs;  *)

    let continue, ldfs = L.simplify_ldfs state maxparams ldfs in
    if continue then 
      let split = find_bij state maxparams ldfs in
      let rec aux (accu:L.ldfs) split (ldfs:L.ldfs) = 
        match split, ldfs with
        | [], [] -> tdone := Z.add !tdone (L.cnp_ldfs accu)
        | (s1, s2) :: split, ldf :: ldfs ->
          let d = ldf.L.n in 
          let len = ldf.L.p in 
          let len1 = List.length s1 in
          if not (d <= len1) then begin
              Format.eprintf "d = %i@." d;
              Format.eprintf "ldf = %a@."
                (pp_list ";  " (fun fmt (e1,_e2) -> pp_expr fmt e1)) ldf.L.l;
              Format.eprintf "s1 = %a@."
                (pp_list ";  " (fun fmt (e1,_e2) -> pp_expr fmt e1)) s1;
            assert false  
          end;
          let len2 = len - len1 in
          aux (L.cons d s1 len1 accu) split ldfs;
          let ldfs = L.rev_append accu ldfs in
          if d <= len2 then 
            check_all state maxparams (L.cons d s2 len2 ldfs);
          for i1 = 1 to d - 1 do
            let i2 = d - i1 in
            if i1 <= len1 && i2 <= len2 then
              check_all state maxparams (L.cons i1 s1 len1 (L.cons i2 s2 len2 ldfs))
          done
        | _ -> assert false in
      aux [] split ldfs 
    else 
      tdone := Z.add !tdone (L.cnp_ldfs ldfs);
   in
  check_all state maxparams ldfs;
  Format.eprintf "%a tuples checked@." pp_z !tdone

exception Done

let check_all_para state maxparams (ldfs:L.ldfs) = 
  let pipe   = Unix.pipe () in
  let tdone  = Shrcnt.create "/masking.para.tdone" in
  let tprcs  = Shrcnt.create "/masking.para.tprcs" in
  let t0     = Sys.time () in
  let parent = ref true in
  let pp     = pp_human "tuples" in

  let cleanup () =
    if !parent then begin
      (try Shrcnt.dispose tdone with _ -> ());
      (try Shrcnt.dispose tprcs with _ -> ())
    end
  in

  try
    let to_check = L.cnp_ldfs ldfs in
  
    Format.eprintf "%a to check@." pp to_check;

    let pid = Unix.fork () in

    if pid = 0 then begin
      Shrcnt.clr_unlink_on_dispose tdone;
      Shrcnt.clr_unlink_on_dispose tprcs;
      parent := false; Unix.close (fst pipe);
      Shrcnt.update tprcs 1L;

      if Unix.fork () <> 0 then exit 0;

      let rec check_all state maxparams (ldfs:L.ldfs) = 
        let continue, ldfs = L.simplify_ldfs state maxparams ldfs in
        if not continue then Shrcnt.update tdone (Z.to_int64 (L.cnp_ldfs ldfs))
        else 
          let nbdone = Shrcnt.get tdone in
          let to_check = Z.sub to_check (Z.of_int64 nbdone) in
          let thld = Z.div to_check (Z.of_int 100) in
          let thld_h = Z.div to_check (Z.of_int 2) in

          let goup, stend = ref false, ref false in

          if Z.gt (L.cnp_ldfs ldfs) thld && Z.lt (L.cnp_ldfs ldfs) thld_h then begin
              if Shrcnt.get tprcs < 4L then begin
                  let pid = Unix.fork () in
                  if pid = 0 then begin
                      if Unix.fork () = 0 then begin
                          stend := true
                        end else begin
                          Shrcnt.update tprcs 1L; exit 0
                        end
                    end else begin
                      goup := true;
                      ignore (Unix.waitpid [] pid : int * _)
                    end
                end
            end;

          if not !goup then begin
            let split = find_bij state maxparams ldfs in
            let rec aux accu split ldfs = 
              match split, ldfs with
              | [], [] ->
                Shrcnt.update tdone (Z.to_int64 (L.cnp_ldfs accu))
                              
              | (s1, s2) :: split, ldf  :: ldfs ->
                let d = ldf.L.n in 
                let len = ldf.L.p in 
                let len1 = List.length s1 in
                let len2 = len - len1 in
                aux (L.cons d s1 len1 accu) split ldfs;
                let ldfs = L.rev_append accu ldfs in
                if d <= len2 then 
                  check_all state maxparams (L.cons d s2 len2 ldfs);
                for i1 = 1 to d - 1 do
                  let i2 = d - i1 in
                  if i1 <= len1 && i2 <= len2 then
                    check_all state maxparams (L.cons i1 s1 len1 (L.cons i2 s2 len2 ldfs))
                done
                  
              | _ -> assert false in
            aux [] split ldfs
          end;

          if !stend then raise Done in

       try
         check_all state maxparams ldfs; raise Done
       with
       | CanNotCheck le -> begin
           Format.eprintf "%a@." print_error le;
           Shrcnt.update tprcs (-1L);
           ignore (Unix.write (snd pipe) "." 0 1 : int);
           exit 1
         end

       | Done -> begin
           Shrcnt.update tprcs (-1L);
           exit 0
         end
      
    end else begin
      Unix.close (snd pipe);
      ignore (Unix.waitpid [] pid : int * _);
      let rec wait () =
        let rds, _, _ = Unix.select [fst pipe] [] [] 5.0 in
        if List.is_empty rds then begin
          Format.eprintf
            "%a checked over %a in %.3f@."
            pp (Z.of_int64 (Shrcnt.get tdone))
            pp to_check (Sys.time () -. t0);
          Format.eprintf
            "# processes : %Ld@." (Shrcnt.get tprcs);
          wait ()
        end else begin
          Unix.read (fst pipe) (Bytes.make 1 '.') 0 1 = 0
        end
      in

      if not (wait ()) then exit 1;
      Format.eprintf "%a checked@." pp (Z.of_int64 (Shrcnt.get tdone));
      if Shrcnt.get tprcs <> 0L then assert false
    end; cleanup ()

  with e -> (cleanup (); raise e)

let check_ni params nb_shares all =
  try 
    let len = List.length all in
    let state = init_state nb_shares params in
    let order = nb_shares - 1 in 
    let all = List.map (fun e -> e, e) all in
    let args = L.cons order all len [] in
    check_all state order args;
    Format.printf "NI@."
  with CanNotCheck le ->
    Format.eprintf "%a@." print_error le

let check_fni ?(para = false) s f params nb_shares interns outs =
  try 
    let len_i = List.length interns in
    let len_o = List.length outs in
    let state = init_state nb_shares params in
    let order = nb_shares - 1 in 
    let interns = List.map (fun e -> e, e) interns in
    let outs = List.map (fun e -> e, e) outs in 
    for ki = 0 to (*nb_shares - 1*) (nb_shares-1)/2 (* FIXME *) do
      let ko = order - ki in
      Format.eprintf "Start checking of ki = %i, ko = %i@." ki ko;
      (if ki <= len_i && ko <= len_o then
         let args = if ko = 0 then [] else L.cons ko outs len_o [] in
         let args = if ki = 0 then args else L.cons ki interns len_i args in
         (if para then check_all_para else check_all) state (f ki ko) args);
      Format.eprintf "Checking of done ki = %i, ko = %i@." ki ko;
    done;
    Format.printf "%s@." s
  with CanNotCheck le ->
    Format.eprintf "%a@." print_error le

let check_sni ?para = check_fni ?para "SNI" (fun ki _ko -> ki)
let check_fni ?para = check_fni ?para "FNI" 

let mk_interns outs = 
  let souts = Se.of_list outs in
  let rec aux interns e = 
    if not (Se.mem e interns) then
      let interns = 
        if not (Se.mem e souts) then Se.add e interns else interns in
      match e.e_node with
      | Eadd(e1,e2) | Emul(e1,e2) -> aux (aux interns e1) e2
      | Etuple(_, es) -> Array.fold_left aux interns es
      | _ -> interns 
    else interns in
  let interns = List.fold_left aux Se.empty outs in
  let res = List.rev (Se.elements interns) in
  List.iter (Format.eprintf "%a@." pp_expr) res;
  res

let main_sni params nb_shares outs = 
  check_sni ~para:false params nb_shares (mk_interns outs) outs

(*let main_ni params nb_shares outs = 
  check_ni params nb_shares (mk_interns outs) outs *)

let main_fni f params nb_shares outs = 
  check_fni f params nb_shares (mk_interns outs) outs

(* ------------------------------------------------------------------ *)

(*
let rec remove_box e = 
  match e.e_node with
  | Eadd(e1,e2) -> add (remove_box e1) (remove_box e2)
  | Emul(e1,e2) -> mul (remove_box e1) (remove_box e2)
  | Ebox e      -> remove_box e
  | _           -> e 

let mk_observation es = 
  let rec aux s e =
     if Se.mem e s then s
     else    
       let s = Se.add e s in
       match e.e_node with
       | Eadd(e1,e2) | Emul(e1,e2) -> aux (aux s e1) e2
       | _ -> s in
  let all = Array.fold_left aux Se.empty es in
  let s = Se.fold (fun e s -> Se.add (remove_box e) s) all Se.empty in
  Se.elements s
         
let main_threshold order params es = 
  try 
    let state = init_state 1 params in
    let all = mk_observation es in
    let all = List.map (fun e -> e, e) all in
    let len = List.length all in
    let args = L.cons order all len [] in
    check_all state 0 args;
    Format.printf "t-threshold secure@."
  with CanNotCheck le ->
    Format.eprintf "%a@." print_error le
*)
(* ------------------------------------------------------------------ *)














