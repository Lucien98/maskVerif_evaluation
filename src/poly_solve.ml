open Util
open Poly
open Expr

module V = struct
  type t = expr
  let equal = E.equal
  let compare = E.compare
              let pp = pp_expr
end

module P = Poly(V)

let to_pol ty tbl =
  let o_add = o_add ty in
  let o_mul = o_mul ty in
  let o_neg = o_neg ty in
  let eone = eone ty in
  let ezero = ezero ty in

  let rec to_pol e =
    try He.find tbl e
    with Not_found ->
      let p =
        match e.e_node with
        | Etop          -> assert false
        | Ernd _ | Eshare _ | Epub _ -> P.var e
        | Econst _ -> 
          if E.equal eone e then P.one
          else if E.equal ezero e then P.zero
          else P.var e
        | Eop1(o, e) when Op.equal o o_neg ->
          P.add P.one (to_pol e) 
        | Eop2(o,e1,e2) when Op.equal o o_add ->
          P.add (to_pol e1) (to_pol e2)
        | Eop2(o,e1,e2) when Op.equal o o_mul ->
          P.mul (to_pol e1) (to_pol e2)
        | Eop(_, o, es) when is_FF_op o -> to_pol es.(1)
        | _ -> assert false (* FIXME error msg *)
      in
      He.add tbl e p;
      p in
  to_pol

let rec split_tuple s e =
  match e.e_node with
  | Eop(_, o, es) when is_op_tuple o ->
    Array.fold_left split_tuple s es
  | _ -> e :: s

exception Depend
exception Found of (expr * P.t)

let rnds excl p =
  let tbl = He.create 101 in
  let add v =
    if He.mem excl v then ()
    else if is_rnd v then He.add tbl v () in
  P.iter_vars add p;
  tbl

let find_rnd excl ps =
  let todo = ref [] in
  let do1 p =
(*    Format.eprintf "find_rnd in %a@." P.pp p; *)
    let rnds = rnds excl p in
(*    Format.eprintf "rnds ok@.";
    He.iter (fun r _ -> Format.eprintf "%a@." pp_expr r) rnds; *)
    let dor r _ =
(*      Format.eprintf "test %a@." pp_expr r; *)
      let (p1, p2, _p3) = P.check_rnd_eucl r p in
      (* p = (r + p1) * p2 + p3 *)
      if not (P.equal p1 P.zero) then
        if (P.equal p2 P.one) then raise (Found (r, p1))
        else todo := (r, p1) :: !todo in
    He.iter dor rnds in
  try List.iter do1 ps; !todo
  with Found rp -> [rp]
     | _ -> assert false

let subst x p p' =
  let q, r = P.divx p' x in
  (* p' = q * x + r *)
  P.add (P.mul q p) r

let no_rnd = P.all_vars (fun e -> not (is_rnd e))

let initial_check_indep k ps =

  let tbl = Hv.create 101 in
  let reset () = Hv.clear tbl in
  let get p =
    try Hv.find tbl p
    with Not_found -> (Sint.empty, 0) in
  let add p i =
    let (si, n) = get p in
    if Sint.mem i si then ()
    else
      let n = n + 1 in
      if k < n then raise Depend
      else
        Hv.replace tbl p (Sint.add i si, n) in
  let rec is_indep1 v =
    match v.e_node with
    | Eshare(p,i,_) -> add p i
    | _ -> () in
  let is_indep depend ps =
    reset ();
    try List.iter (P.iter_vars is_indep1) depend;
        List.iter (P.iter_vars is_indep1) ps; true
    with Depend -> false in

  let rec aux excl depend ps =
    (* Format.eprintf "aux@.";
    Format.eprintf "depend = @[<v>%a@]@." (pp_list "@ " P.pp) depend;
    Format.eprintf "ps = @[<v>%a@]@." (pp_list "@ " P.pp) ps;
 *)
    if is_indep depend ps then true
    else
      match find_rnd excl ps with
      | [] -> Format.eprintf "No rnd rule@."; false
      | (r,p) :: _ ->
        (* Format.eprintf "r = %a; p = %a@." pp_expr r P.pp p; *)
        He.add excl r ();
        let ps = List.map (subst r (P.add (P.var r) p)) ps in
        let dps, ps = List.partition no_rnd ps in
        aux excl (List.rev_append dps depend) ps in

  aux (He.create 101) [] ps

let check_indep k (es:expr list) =

  let pol_tbl = He.create 101 in
  let ty = match es with e::_ -> Pexpr.find_ty e | _ -> assert false in
  let to_pol = to_pol ty pol_tbl in
  let ps =
    let to_pols s e =
      let es = split_tuple [] e in
      List.fold_left (fun s e -> to_pol e :: s) s es in
    List.fold_left to_pols [] es in

  initial_check_indep k ps
