open Util

type var = {
  v_id   : int;
  v_name : string;
}

module V = struct 

  let id = ref 0 

  let mk_var s =
    let p = { v_id = !id; v_name = s } in
    incr id;
    p 
    
  let clone v = mk_var v.v_name

  type t = var 

  let equal v1 v2 = v1 == v2

  let hash v = v.v_id

  let compare v1 v2 = v1.v_id - v2.v_id
    
end

module Sv = Set.Make(V)
module Mv = Map.Make(V)
module Hv = Hashtbl.Make(V)

(* ----------------------------------------------------------------------- *)

type rnd = var
type param = var 

let pp_var fmt v = Format.fprintf fmt "%s" v.v_name 

let pp_rnd fmt r = Format.fprintf fmt "$%a" pp_var r

let pp_share fmt (p,s,v) = 
  Format.fprintf fmt "%a.[%i]/%a/" pp_var p s pp_var v

(* ----------------------------------------------------------------------- *)

type operator = hstring 

type expr = {
  e_id : int;
  e_node : expr_node}

and expr_node = 
| Etop
| Ernd   of rnd
| Eshare of param * int * var (* the var is the original name *)
| Epub   of var 
| Eneg   of expr
| Eadd   of expr * expr
| Emul   of expr * expr
| Eop of bool * operator * expr array
  (* Invariant [Eop(b,es)]
       if b is true there is no duplicate in the array es *)

let e_equal e1 e2 = e1 == e2
let e_hash e = e.e_id

module HE = struct

  type t = expr

  let equal_node n1 n2 = 
    match n1, n2 with 
    | Etop         , Etop          -> true
    | Ernd r1      , Ernd r2       -> V.equal r1 r2
    | Eshare(p1,i1,v1), Eshare(p2,i2,v2) -> 
      i1 == i2 && V.equal p1 p2 && V.equal v1 v2
    | Epub x1      , Epub x2       -> V.equal x1 x2 
    | Eneg e1      , Eneg e2       -> e_equal e1 e2
    | Eadd(e11,e12), Eadd(e21,e22) -> e_equal e11 e21 && e_equal e12 e22
    | Emul(e11,e12), Emul(e21,e22) -> e_equal e11 e21 && e_equal e12 e22
    | Eop(b1,o1,es1), Eop(b2,o2,es2) -> 
      b1 = b2 && HS.equal o1 o2 && Array.for_all2 e_equal es1 es2
    | _                            -> false

  let equal e1 e2 = equal_node e1.e_node e2.e_node 

  let combine h tag = h lsl 3 + tag
  let combine2 h1 h2 tag = combine (combine h1 h2) tag

  let hash_node = function
    | Etop        -> 0
    | Ernd r      -> combine (V.hash r) 1
    | Eshare(p,i,v) -> combine2 (combine (V.hash v) (V.hash p)) i 2
    | Epub x      -> combine (V.hash x) 3
    | Eneg e1     -> combine (e_hash e1) 4 
    | Eadd(e1,e2) -> combine2 (e_hash e1) (e_hash e2) 5
    | Emul(e1,e2) -> combine2 (e_hash e1) (e_hash e2) 6 
    | Eop(_b,o,es)   -> 
      let h = 
        Array.fold_left (fun h e -> combine h (e_hash e)) (HS.hash o) es in
      combine h 7

  let hash e = hash_node e.e_node

end

module E = struct 

  module W = Weak.Make(HE)

  let id = ref 0 
  let h = W.create 5000

  let mk_expr e =
    let e = { e_id = -1; e_node = e } in
    try W.find h e 
    with Not_found ->
      let e = { e with e_id = !id } in
      W.add h e; incr id;
      e

  type t = expr

  let equal e1 e2 = e1 == e2

  let hash e = e.e_id

  let compare e1 e2 = e1.e_id - e2.e_id
    
end

module He = Hashtbl.Make(E)

module Se = Set.Make(E)

module Me = Map.Make(E)

let top       = E.mk_expr Etop
let rnd r     = E.mk_expr (Ernd r)
let pub x     = E.mk_expr (Epub x) 
let share p i v = E.mk_expr (Eshare(p,i,v))
let neg e     = E.mk_expr (Eneg e)
let add e1 e2 = E.mk_expr (Eadd(e1,e2))
let mul e1 e2 = E.mk_expr (Emul(e1,e2))

let unsafe_op b o es = E.mk_expr (Eop(b,o,es))

let op_nodup o es = E.mk_expr (Eop(true,o, es))

let op o es  =
  let n = Array.length es in
  let tbl = He.create (2 * n) in
  let rec check i =
    n <= i || 
      (not (He.mem tbl es.(i)) &&
         (He.add tbl es.(i) ();check (i+1))) in
  let b = check 0 in
  unsafe_op b o es 

let is_op_tuple o = HS.equal o _TUPLE_

let tuple_nodup es = op_nodup _TUPLE_ es

let tuple es = op _TUPLE_ es

let etrue = op (HS.make "1'1") [||]
let efalse = op (HS.make "1'0") [||]

let is_rnd e = 
  match e.e_node with
  | Ernd _ -> true
  | _      -> false
  
(* --------------------------------------------------------------------- *)
let pp_expr fmt e =
  let rec aux top fmt e = 
    match e.e_node with
    | Etop        -> Format.fprintf fmt "TOP"
    | Ernd r      -> pp_rnd fmt r
    | Eshare(p,i,v) -> pp_share fmt (p,i,v)
    | Epub x      -> pp_var fmt x
    | Eneg e      -> 
      Format.fprintf fmt "!%a" (aux `Not) e
    | Eadd(e1,e2) -> 
      begin match top with
      | `AddR | `MulL | `MulR | `Not ->
        Format.fprintf fmt "(%a + %a)" (aux `AddL) e1 (aux `AddR) e2
      | _ -> 
        Format.fprintf fmt "%a + %a" (aux `AddL) e1 (aux `AddR) e2
      end
    | Emul(e1,e2) -> 
      begin match top with
      | `MulR | `Not -> 
        Format.fprintf fmt "(%a * %a)" (aux `MulL) e1 (aux `MulR) e2
      | _ ->
        Format.fprintf fmt "%a * %a" (aux `MulL) e1 (aux `MulR) e2
      end 
    | Eop(_, o, es) ->
      if Array.length es <> 0 then
        Format.fprintf fmt "%s(@[<hov 2>%a@])" o.hs_str
          (pp_list ",@ " (aux `Top)) (Array.to_list es) 
      else 
        Format.fprintf fmt "%s" o.hs_str in
  aux `Top fmt e

(* ------------------------------------------------------------------------ *)
(* Boolean checker for independance                                         *)

type result = 
  | Rb of bool
  | Rtuple of result array

type env = bool He.t 
    
let get_val env e = 
  try He.find env e with Not_found -> assert false

let eval_bool env e = 
  let tbl = He.create 107 in
  let rec eval_bool e = 
    try He.find tbl e 
    with Not_found -> 
      let res = match e.e_node with
        | Etop -> assert false 
        | Ernd _ | Eshare _ -> Rb (get_val env e)
        | Epub _ -> Rb true (* FIXME : assert false *)
        | Eneg e -> 
          begin match eval_bool e with
          | Rb b -> Rb (not b)
          | _    -> assert false
          end
        | Eadd (e1,e2) -> 
          begin match eval_bool e1, eval_bool e2 with
          | Rb b1, Rb b2 -> Rb (if b1 then not b2 else b2)
          | _, _         -> assert false
          end
        | Emul (e1,e2) -> 
          begin match eval_bool e1 with
          | Rb false -> Rb false
          | Rb true -> eval_bool e2
          | _       -> assert false
          end
        | Eop (_, o, es) ->
          if is_FF_op o then eval_bool es.(1)
          else if is_op_tuple o then Rtuple (Array.map eval_bool es)
          else if E.equal e etrue then Rb true 
          else if E.equal e efalse then Rb false 

          else 
            (Format.eprintf "cannot evaluate bool: %a@." pp_expr e;
             assert false) in
      He.add tbl e res;
      res in
  eval_bool e


exception CheckBool 

let check_bool (opt:tool_opt) e = 
  assert (opt.checkbool);
  (* compute the params and the randoms *)
  let hp = He.create 10 in
  let hr = He.create 100 in
  Format.eprintf "Start boolean checking@.";
  if opt.pp_error then Format.eprintf "%a@." pp_expr e; 
  let rec aux e = 
    match e.e_node with
    | Etop -> assert false
    | Ernd _ -> He.replace hr e true
    | Eshare _ -> He.replace hp e true 
    | Epub _ -> () (* FIXME 
                 Format.eprintf "pub %a@." pp_expr e; assert false *)
    | Eneg e -> aux e
    | Eadd (e1,e2) | Emul (e1,e2) -> aux e1; aux e2
    | Eop (_, o, es) ->
      if HS.equal o _DFF_PP0_ then        aux es.(1)
      else if HS.equal o _DFFSR_PPP_ then aux es.(1)
      else if HS.equal o _TUPLE_ then     Array.iter aux es
      else assert (E.equal e etrue || E.equal e efalse) in
  aux e;
  let rs = He.fold (fun e _ els -> e::els) hr [] in
  let ps = He.fold (fun e _ els -> e::els) hp [] in
  let get tbl e = try Hashtbl.find tbl e with Not_found -> 0 in
  let lps, lrs = List.length ps, List.length rs in
  Format.eprintf "Start boolean checking ps = %i; rs = %i@." lps lrs;
  let env = hr in
  List.iter (fun e -> He.replace env e true) ps;

  let check_r rs = 
    Format.eprintf "."; Format.pp_print_flush Format.err_formatter ();
    let rtbl = Hashtbl.create 100 in
    let add res = Hashtbl.replace rtbl res (get rtbl res + 1) in
    let rec check_r rs = 
      match rs with
      | [] -> add (eval_bool env e)
      | r::rs -> 
        He.replace hr r true; check_r rs;
        He.replace hr r false; check_r rs in
    check_r rs;

    rtbl in
  let ttbl = check_r rs in
  let check_tbl rtbl = 
    let check_tr e n =
      if n <> get rtbl e then 
        raise CheckBool in
    Hashtbl.iter check_tr ttbl;
    let check_rt e n = 
      if n <> get ttbl e then 
        raise CheckBool in
    Hashtbl.iter check_rt rtbl in
  let rec check_p ps = 
    match ps with
    | [] -> check_tbl (check_r rs) 
    | p::ps -> 
        He.replace hr p true; check_p ps;
        He.replace hr p false; check_p ps in
  check_p ps;
  Format.eprintf "@."


