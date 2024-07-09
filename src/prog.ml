(* --------------------------------------------------------------------
 * Copyright (c) - 2012--2018 - Inria
 *
 * Distributed under the terms of the CeCILL-C-V1 license
 * -------------------------------------------------------------------- *)
open Util

module P = Parsetree
module E = Expr

type var = E.var

type expr =
  | Evar of var
  | Econst of E.constant
  | Eop1 of E.operator * expr 
  | Eop2 of E.operator * expr * expr
  | Eop  of E.operator * expr list
  | Ebox of E.expr

(* ---------------------------------------------------------------------- *)
let type_of_expr e = 
  match e with 
  | Evar v -> Some v.v_ty
  | Econst c -> Some c.c_ty
  | Eop1(op,_) | Eop2(op,_,_) | Eop(op,_) -> 
    begin match op.op_ty with
    | Some(_,codom) -> Some(codom)
    | None -> None
    end
  | Ebox e -> E.type_of_expr e


type assgn = {i_var : var; i_kind : P.instr_kind; i_expr : expr }

type vcall = var list

type vcalls = vcall list

type fname = HS.t

type macro_call = { i_lhs : vcalls; i_macro: fname; i_args : vcalls }

type leak = {l_name : var; l_exprs : expr list}

type instr_d =
  | Ileak of leak
  | Iassgn of assgn
  | Imacro of macro_call

type instr = {
    instr_d : instr_d;
    instr_info : Format.formatter -> unit -> unit;
  }

type cmd = instr list

type func = {
  f_name   : HS.t;
  f_pin    : var list;
  f_in     : (var * var list) list;
  f_out    : var list list;
  f_other  : var list;
  f_rand   : var list;
  f_cmd    : cmd }

(* ------------------------------------------------------------------- *)
(* Pretty printing                                                     *)

type print_info = {
    var_full   : bool;
    print_info : bool;
  }

let dft_pinfo = {
    var_full    = false;
    print_info  = false;
  }

let var_pinfo = {
    var_full    = true;
    print_info  = false;
  }

let pp_var ?(full=dft_pinfo) fmt x =
  let pp_id fmt i =
    if full.var_full then Format.fprintf fmt "#%i" i in
  Format.fprintf fmt "%s%a" x.E.v_name pp_id x.E.v_id


let pp_expr ?(full=dft_pinfo) fmt e =
  let rec aux top fmt e =
    match e with
    | Evar x        -> pp_var ~full fmt x
    | Econst c      -> E.C.pp fmt c
    | Eop1(o, e )   -> E.pp_op1 aux fmt o e
    | Eop2(o,e1,e2) -> E.pp_op2 aux fmt top o e1 e2
    | Eop(o,es)     -> E.pp_op aux fmt o (Array.of_list es)
    | Ebox e        -> Format.fprintf fmt "[%a]" E.pp_expr e in
  aux `Top fmt e

let pp_assgn ?(full=dft_pinfo) fmt i =
  begin match i.i_kind with
  | P.IK_subst ->
    Format.fprintf fmt "@[<hov 2> %a :=@ %a@]"
  | P.IK_hide ->
    Format.fprintf fmt "@[<hov 2> %a =@ {%a}@]"
  | P.IK_sub ->
    Format.fprintf fmt "@[<hov 2> %a =@ %a@]"
  | P.IK_glitch ->
    Format.fprintf fmt "@[<hov 2> %a =@ ![%a]@]"
  | P.IK_noleak ->
    Format.fprintf fmt "@[<hov 2> %a <-@ {%a}@]"
  end
     (pp_var ~full) i.i_var (pp_expr ~full) i.i_expr

let pp_vars ?(full=dft_pinfo) fmt xs =
  Format.fprintf fmt "@[<hov>%a@]" (pp_list ",@ " (pp_var ~full)) xs

let pp_vcall ?(full=dft_pinfo) fmt xs =
  Format.fprintf fmt "[%a]" (pp_vars ~full) xs

let pp_vcalls ?(full=dft_pinfo) fmt xs =
  Format.fprintf fmt "@[<hov>(%a)@]"
    (pp_list ",@ " (pp_vcall ~full)) xs

let pp_call ?(full=dft_pinfo) fmt i =
  Format.fprintf fmt "@[<hov 2> %a =@ %a%a@]"
    (pp_vcalls ~full) i.i_lhs (HS.pp full.var_full) i.i_macro (pp_vcalls ~full) i.i_args

let pp_exprs ?(full=dft_pinfo) fmt es =
  Format.fprintf fmt "@[<hov>%a@]"
    (pp_list ",@ " (pp_expr ~full)) es

let pp_leak ?(full=dft_pinfo) fmt i =
  Format.fprintf fmt "@[<hov 2> leak %a |=@ (%a)@]"
    (pp_var ~full) i.l_name (pp_exprs ~full) i.l_exprs

let pp_instr_d ?(full=dft_pinfo) fmt = function
  | Iassgn i -> pp_assgn ~full fmt i
  | Imacro i -> pp_call ~full fmt i
  | Ileak i -> pp_leak ~full fmt i

let pp_instr ?(full=dft_pinfo) fmt i =
  let pp_info fmt i = if full.print_info then i.instr_info fmt () in
  Format.fprintf fmt "%a%a" pp_info i (pp_instr_d ~full) i.instr_d

let pp_cmd ?(full=dft_pinfo) fmt c =
  Format.fprintf fmt "@[<v>%a@]" (pp_list "@ " (pp_instr ~full)) c

let pp_decls ?(full=dft_pinfo) fmt xs =
  Format.fprintf fmt "@[<hov>%a@]" (pp_list ",@ " (pp_vcall ~full)) xs

let pp_indecls ?(full=dft_pinfo) fmt xs =
  let pp fmt (x,xs) =
    Format.fprintf fmt "(%a, %a)" (pp_var ~full) x (pp_vcall ~full) xs in
  Format.fprintf fmt "@[<hov>%a@]" (pp_list ",@ " pp) xs

let pp_func ?(full=dft_pinfo) fmt func =
  Format.fprintf fmt "@[<v>proc %s:@   " func.f_name.hs_str;
  Format.fprintf fmt "@[<v>";
  Format.fprintf fmt "@[<hov>public inputs: @[%a@]@]@ "
    (pp_list ",@ " (pp_var ~full)) func.f_pin;

  Format.fprintf fmt "@[<hov>inputs : @[%a@]@]@ " (pp_indecls ~full) func.f_in;
  Format.fprintf fmt "@[<hov>outputs: @[%a@]@]@ " (pp_decls ~full) func.f_out;
  Format.fprintf fmt "@[<hov>randoms: @[%a@]@]@ "
    (pp_list ",@ " (pp_var ~full)) func.f_rand;
  Format.fprintf fmt "@[<hov>others : @[%a@];@]@ @ "
    (pp_list ",@ " (pp_var ~full)) func.f_other;
  pp_cmd ~full fmt func.f_cmd;
  Format.fprintf fmt "@]@]"

let pp_prog ?(full=dft_pinfo) fmt prog =
  Format.fprintf fmt "@[<v>%a@]"
    (pp_list "@ @ " (pp_func ~full)) prog

(* ------------------------------------------------------------------------ *)
(* Translation from Parsetree to Prog *)

let error loc = error "Type error" (Some loc)

type global_env = (string, func) Hashtbl.t

let add_global globals func =
  Hashtbl.add globals func.f_name.hs_str func

let get_global globals id =
  try Hashtbl.find globals (data id)
  with Not_found ->
    error (loc id) "undeclared macro %a" P.pp_ident id

module ToProg = struct
  type vkind =
    | VKvar of var
    | VKtuple  of var list

  type env = {
      globals: global_env;
      mutable locals : vkind P.Mid.t;
      mutable others : var list;
      mutable init   : E.Sv.t
    }

  let add_var other env id kind =
    if P.Mid.mem id env.locals then
      error (loc id) "multiple declaration of %a" P.pp_ident id;
    env.locals <- P.Mid.add id kind env.locals;
    match other, kind with
    | true, VKvar x -> env.others <- x::env.others
    | _ -> ()

  let get_vars env id =
    let k =
      try P.Mid.find id env.locals
      with Not_found ->
        let k = VKvar (E.V.mk_var (data id) E.w1 ) in
        add_var true env id k;
        k in
    match k with
    | VKvar x -> [x]
    | VKtuple xs -> xs

  let check_single loc id xs =
    match xs, id with
    | [x], _ -> x
    | _, Some id ->
      error loc "the variable %a is a shared variable" P.pp_ident id
    | _, None ->
      error loc "shared variable not allowed here"

  let get_var env id =
    check_single (loc id) (Some id) (get_vars env id)

  let mk_range id (i,j) =
    List.map (fun i -> {id with pl_data = (data id^ string_of_int i)})
      (mk_range_i i j)

  let mk_rangen id rs =
    List.flatten (List.map (mk_range id) rs)

  let get_vcall1 env vcall =
    match vcall with
    | P.Vid(id,None) -> get_vars env id
    | P.Vid(id,Some r) ->
      let ids = mk_rangen id r in
      List.map (get_var env) ids
    | P.Vtuple ids ->
      List.map (get_var env) (data ids)

  let rotate_xs dir xs i =
    let n = List.length xs in
    let i = i mod n in
    if i = 0 then xs
    else
      let l1, l2 = if dir = `Right then n-i, i else i, n-i in
      let xs = Array.of_list xs in
      let xs1 = Array.sub xs 0 l1 in
      let xs2 = Array.sub xs l1 l2 in
      let xs = Array.append xs2 xs1 in
      Array.to_list xs

  let get_vcall env (vc1, shf) =
    let xs = get_vcall1 env vc1 in
    match shf with
    | None -> xs
    | Some (P.Sr i) -> rotate_xs `Right xs i
    | Some (P.Sl i) -> rotate_xs `Left xs i

  let check_init env loc xs =
    let l = List.filter (fun x -> not (E.Sv.mem x env.init)) xs in
    match l with
    | [] -> ()
    | [x] -> error loc "variable %a is not initialized" (pp_var ~full:dft_pinfo)x
    | xs  -> error loc "variables %a are not initialized"
               (pp_list ",@ " (pp_var ~full:dft_pinfo)) xs

  let get_op op = 
    try E.Op.find (data op) 
    with Not_found -> error (loc op) "unknown operator : %s" (data op)

  let check_ty_e loc e ty = 
    match type_of_expr e with
    | Some ty' -> 
      if ty <> ty' then 
        error loc "the expression has type %s instead of %s" 
          (E.ty2string ty') (E.ty2string ty)
    | None ->
      error loc "the expression should have type %s" 
        (E.ty2string ty)

  let rec to_expr env e =
    match data e with
    | P.Evar v ->
      let xs = get_vcall env v in
      let loc = P.vcall_loc v in
      let x = check_single loc None xs in
      check_init env loc xs;
      Evar x
    | P.Econst (l,ty) -> Econst (E.C.make ty (data l))
    | P.Eop(op,es) -> 
      let op = get_op op in
      begin match op.op_ty with
      | None -> assert false
      | Some(dom, _codom) ->
        let es = List.map2 (to_expr_ty env) es dom in
        match es with
        | [e]     -> Eop1(op, e)
        | [e1;e2] -> Eop2(op,e1,e2)
        | _       -> Eop(op,es)
      end
  and to_expr_ty env e ty =
    let e' = to_expr env e in
    check_ty_e (loc e) e' ty;
    e'
 
  let rec to_expr_n env n e =
    match data e with
    | P.Evar x ->
      let xs = get_vcall env x in
      let loc = P.vcall_loc x in
      check_init env loc xs;
      let n' = List.length xs in
      if n' <> n then
        error loc "%a contains %i elements while %i is execpted"
          P.pp_vcall x n' n;
      List.map (fun x -> Evar x) xs
    | P.Econst(l,ty) ->
      List.init n (fun _ -> Econst (E.C.make ty (data l)))
    | P.Eop(op,es) ->
      let op = get_op op in
      begin match op.op_ty with
      | None -> assert false
      | Some(dom, _codom) -> 
        let es = List.map2 (to_expr_n_ty env n) es dom in
        match es with
        | [] -> List.init n (fun _ -> Eop(op,[]))
        | [e] -> List.map (fun e -> Eop1(op,e)) e
        | [e1;e2] -> List.map2 (fun e1 e2 -> Eop2(op,e1,e2)) e1 e2
        | es ->
          List.init n (fun i -> Eop(op, List.map (fun e -> List.nth e i) es))
      end
  and to_expr_n_ty env n e ty =
    let e' = to_expr_n env n e in
    List.iter (fun e' -> check_ty_e (loc e) e' ty) e';
    e'
    

  let set_init env x =
    env.init <- E.Sv.add x env.init

  let get_vcalls env id vcalls pins ins =
    let pl1 = List.length pins in
    let l1 = List.length ins in
    let l2 = List.length vcalls in
    if (pl1 + l1) <> l2 then
      error (loc id)
        "the function %a expects %i arguments while %i are provided"
        P.pp_ident id (pl1 + l1) l2;

    let pub, vcalls = List.split pl1 vcalls in
    let get_pub v =
      let xs = get_vcall env v in
      let loc = P.vcall_loc v in
      match xs with
      | [_] -> xs
      | _   -> error loc "shared variable not allowed here" in

    let pub = List.map get_pub pub in

    let get_vcall v (_,in_) =
      let xs = get_vcall env v in
      let loc = P.vcall_loc v in
      let l1 = List.length xs in
      let l2 = List.length in_ in
      if l1 <> l2 then
        error loc
          "%a contains %i shares while %i is expected"
          P.pp_vcall v l1 l2;
      check_init env loc xs;
      xs in
    let ins = List.map2 (get_vcall) vcalls ins in
    pub @ ins


  let set_vcalls env id vcalls outs =
    let l1 = List.length outs in
    let l2 = List.length vcalls in
    if l1 <> l2 then
      error (loc id)
        "the function %a return %i elements while %i are provided"
        P.pp_ident id l1 l2;
    let set_vcall v out =
      let xs = get_vcall env v in
      let loc = P.vcall_loc v in
      let l1 = List.length xs in
      let l2 = List.length out in
      if l1 <> l2 then
        error loc
          "%a contains %i shares while %i is expected"
          P.pp_vcall v l1 l2;
      List.iter (set_init env) xs;
      xs in
    List.map2 (set_vcall) vcalls outs

  let vars =
    let rec aux fv = function
      | Evar x -> E.Sv.add x fv
      | Eop1(_, e) -> aux fv e 
      | Eop2(_,e1,e2) -> aux (aux fv e1) e2
      | Eop(_,es) -> List.fold_left aux fv es
      | Ebox _ | Econst _ -> fv in
    aux E.Sv.empty

  let check_para loc is =
    let assigned = ref E.Sv.empty in
    let check i =
      match i.instr_d with
      | Iassgn i ->
        let inter = E.Sv.inter (vars i.i_expr) !assigned in
        if not (E.Sv.is_empty inter) then
          error loc
            "invalid parrallel assignment: variables %a are used in both side"
            (pp_list ", " (pp_var ~full:dft_pinfo)) (E.Sv.elements inter);
        assigned := E.Sv.add i.i_var !assigned
      | _ -> assert false in
    List.iter check is

  let pp_loc_info loc msg fmt () =
    if msg = "" then
      Format.fprintf fmt "(* %s *)@ " (Location.to_string loc)
    else 
      Format.fprintf fmt "@[<v>(* %s@    %s *)@]" (Location.to_string loc) msg

  let mk_instr loc ?(msg="") i = {
      instr_d = i;
      instr_info = pp_loc_info loc msg;
    }


  let to_assgn env i =
    let loc = loc i in
    let i = data i in
    let xs = get_vcall env i.P.i_var in
    let mk_assgn x e =
      set_init env x;
      mk_instr loc (Iassgn { i_var  = x; i_kind = i.P.i_kind; i_expr = e }) in
    match xs with
    | [x] -> [mk_assgn x (to_expr env i.P.i_expr)]
    | xs ->
      let es = to_expr_n env (List.length xs) i.P.i_expr in
      let is = List.map2 mk_assgn xs es in
      check_para (P.vcall_loc i.P.i_var) is;
      is

  let check_disjoint id xss yss =
    let o = E.Hv.create 101 in
    let do1 x =
      if E.Hv.mem o x then
        warning ~loc:(loc id)
          "the variable %a is used multiple time in function call %a, must leads to unexpected behavior" (pp_var ~full:dft_pinfo) x P.pp_ident id;
      E.Hv.replace o x () in
    let don = List.iter (List.iter do1) in
    don xss;
    don yss

  let to_macro env i =
    let loc = loc i in
    let i = data i in
    let id = i.P.i_macro in
    let f = get_global env.globals id in
    let i_macro = f.f_name in
    let i_args = get_vcalls env id i.P.i_args f.f_pin f.f_in in
    let i_lhs = set_vcalls env id i.P.i_lhs f.f_out in
    check_disjoint id i_args i_lhs;
    [mk_instr loc (Imacro { i_lhs; i_macro; i_args })]

  let get_lexprs env es =
    List.map (to_expr env) es

  let to_leak env i =
    let loc = loc i in
    let (i,msg) = data i in
    let lname = get_var env i.P.l_name in
    let les = get_lexprs env i.P.l_exprs in
    set_init env lname;
    [mk_instr loc ~msg (Ileak { l_name = lname; l_exprs = les })]

  let to_instr env i =
    match (data i) with
    | P.Iassgn id -> to_assgn env (mkloc (loc i) id)
    | P.Imacro id -> to_macro env (mkloc (loc i) id)
    | P.Ileak (id,msg) -> to_leak env (mkloc (loc i) (id,msg))

  let set_rand env (id,orng, ty) =
    let doit id =
      let x = E.V.mk_var (data id) ty in
      add_var false env id (VKvar x);
      set_init env x;
      x in
    match id,orng with
    | id, None -> [doit id]
    | id, Some r ->
      let xs = List.map doit (mk_range id r) in
      add_var false env id (VKtuple xs);
      xs

  let set_shared other env (id,ids,ty) =
    let add id =
      let x = E.V.mk_var (data id) ty in
      add_var other env id (VKvar x);
      x in
    let ids =
      match ids with
      | P.Ids ids -> ids
      | P.Range r -> mk_range id r in
    let xs = List.map add ids in
    let x = E.V.mk_var (data id) ty in
    add_var other env id (VKtuple xs);
    x, xs

  let set_shared_init other env ids =
    let (_, xs as xxs) = set_shared other env ids in
    List.iter (set_init env) xs;
    xxs

  let init_shared globals func =
    let env = { globals = globals;
                locals = P.Mid.empty;
                others = [];
                init = E.Sv.empty } in

    let f_in = List.map (set_shared_init false env) func.P.f_in in
    let f_ou = List.map (set_shared false env) func.P.f_out in
    let f_ou = List.map snd f_ou in
    let _    = List.map (set_shared true env) func.P.f_shares in
    let f_pin = List.flatten (List.map (set_rand env) func.P.f_pin) in
    let rnds = List.flatten (List.map (set_rand env) func.P.f_rand) in
    env, f_pin, f_in, f_ou, rnds

  let to_func globals func =
    let f_name = HS.make (data func.P.f_name) in
    let env, f_pin, f_in, f_out, f_rand = init_shared globals func in
    let f_cmd = List.flatten (List.map (to_instr env) func.P.f_cmd) in
    let f_other = env.others in
    { f_name; f_pin; f_in; f_out; f_other; f_rand; f_cmd }

end
(* ------------------------------------------------------------------ *)

module Process = struct
  let rename_var s x =
    try E.Hv.find s x with Not_found -> assert false

  let rec rename_e s e =
    match e with
    | Evar x -> Evar (rename_var s x)
    | Econst c -> Econst c
    | Eop1(op,e) -> Eop1(op, rename_e s e)
    | Eop2(op,e1,e2) -> Eop2(op, rename_e s e1, rename_e s e2)
    | Eop(o, es)   -> Eop(o, List.map (rename_e s) es)
    | Ebox _       -> assert false

  let rename_i ppi s ii =
    let d =
      match ii.instr_d with
      | Iassgn i ->
        Iassgn { i with i_var = rename_var s i.i_var;
                        i_expr = rename_e s i.i_expr }
      | Imacro i ->
        let rename_vcalls = List.map (List.map (rename_var s)) in
        Imacro { i_lhs   = rename_vcalls i.i_lhs;
                 i_macro = i.i_macro;
                 i_args  = rename_vcalls i.i_args }
      | Ileak i ->
        let rename_exprs = List.map (rename_e s) in
        Ileak { l_name = rename_var s i.l_name;
                l_exprs = rename_exprs i.l_exprs
              } in
    { instr_d = d;
      instr_info = fun fmt () -> ppi fmt (); ii.instr_info fmt ();
    }

  (* ------------------------------------------------------------------ *)

  type env_expand = {
      ee_globals : global_env;
      mutable rnd : var list;
      mutable other : var list;
    }

  let get_macro env fname =
    try Hashtbl.find env.ee_globals fname.hs_str
    with Not_found -> assert false

  let macro_expand_call ppi env i =
    let func = get_macro env i.i_macro in
    let s = E.Hv.create 57 in
    let add x y = E.Hv.add s x y in
    let adds xs ys = List.iter2 add xs ys in
    (* FIXME: public args ... *)
    List.iter2 adds
      ((List.map (fun x -> [x]) func.f_pin) @
       (List.map snd func.f_in)) i.i_args;
    List.iter2 adds func.f_out i.i_lhs;
    let add_clone x = let x' = E.V.clone x in add x x'; x' in
    let add_rnd x   = let x' = add_clone x in env.rnd <- x'::env.rnd in
    let add_other x = let x' = add_clone x in env.other <- x'::env.other in
    List.iter add_rnd func.f_rand;
    List.iter add_other func.f_other;
    List.map (rename_i ppi s) func.f_cmd

  let rec macro_expand_c env c =
    match c with
    | [] -> []
    | { instr_d = Iassgn _ } as i :: c -> i :: macro_expand_c env c
    | { instr_d = Imacro i} as ii :: c ->
      let c = macro_expand_c env c in
      let ic = macro_expand_call ii.instr_info env i in
      ic@c
    | { instr_d = Ileak _ } as i :: c -> i :: macro_expand_c env c

  let macro_expand_func globals func =
    let env = {
        ee_globals = globals;
        other = func.f_other;
        rnd   = func.f_rand;
      } in
    let c = macro_expand_c env func.f_cmd in
    { func with
      f_other = env.other;
      f_rand  = env.rnd;
      f_cmd   = c }

  let func globals f =
    let func = ToProg.to_func globals f in
    let func = macro_expand_func globals func in
    add_global globals func;
    func

end

(* ------------------------------------------------------------------ *)
(* Buildind the set of possible observations *)
(*
  x = { e } // pas de glitches
  x := e1 op e2 // genere des glitches
  x != e   // stop les glitch
  x <- e
*)

let rec expr_of_pexpr e =
  match e with
  | Evar _           -> assert false
  | Econst c         -> E.econst c
  | Eop1(op, e)      -> E.op1 op (expr_of_pexpr e)
  | Eop2(op, e1, e2) -> E.op2 op (expr_of_pexpr e1) (expr_of_pexpr e2)
  | Eop(o, es)       ->
    E.op o (Array.of_list (List.map expr_of_pexpr es))
  | Ebox e           -> e

let subst_v s x =
  try E.Hv.find s x
  with Not_found ->
    Format.eprintf "Can not find %a@." (pp_var ~full:dft_pinfo) x;
    assert false

let rec subst_e s e =
  match e with
  | Evar x         -> subst_v s x
  | Econst c       -> Econst c
  | Eop1(op,e)     -> Eop1(op, subst_e s e)
  | Eop2(op,e1,e2) -> Eop2(op, subst_e s e1, subst_e s e2)
  | Eop(o, es)     -> Eop(o, List.map (subst_e s) es)
  | Ebox e         -> Ebox e

let fv =
  let rec aux fv e =
    match e with
    | Evar _        -> assert false
    | Econst _      -> fv
    | Eop1(_,e)     -> aux fv e
    | Eop2(_,e1,e2) -> aux (aux fv e1) e2
    | Eop(_,es)     -> List.fold_left aux fv es
    | Ebox e        -> E.Se.add e fv in
  aux E.Se.empty

type obs_info = Format.formatter -> unit -> unit

type observation = obs_info E.He.t

let add_observation obs e pp =
  if not (E.He.mem obs e) then
    E.He.add obs e pp

let rec add_sub obs e pp =
  match e with
  | Evar _ -> assert false (* Variables are boxed in Ebox *)
  | Econst c -> E.econst c
  | Eop1(op, e) ->
    let e = add_sub obs e pp in
    (* For bijective unarity operator not we do not add "op e", 
       since the adversary can directly observe e *)
    let e = E.op1 op e in
    if not op.E.op_bij then add_observation obs e pp;
    e
  | Eop2(op,e1,e2) ->
    let e1 = add_sub obs e1 pp in
    let e2 = add_sub obs e2 pp in
    let e = E.op2 op e1 e2 in
    add_observation obs e pp;
    e
  | Eop(o,es) ->
    let doit e = add_sub obs e pp in
    let es = List.map doit es in
    let e = E.op o (Array.of_list es) in
    add_observation obs e pp;
    e
  | Ebox e ->
    add_observation obs e pp;
    e

let add_trans obs etrans e pp =
  match etrans with
  | None -> ()
  | Some et ->
    let e =
      if E.E.equal et e then e
      else E.tuple_nodup [|et; e|] in
    add_observation obs e pp

let glitch_expr etrans e =
  let fv = fv e in
  let fv =
    match etrans with
    | None -> fv
    | Some e -> E.Se.add e fv in
  let els = Array.of_list (E.Se.elements fv) in
  if Array.length els = 1 then els.(0)
  else E.tuple_nodup els

let add_glitch obs etrans e pp =
  add_observation obs (glitch_expr etrans e) pp

let rec remove_top_not e =
  match e.E.e_node with
  | E.Eop1(op, e) when op.E.op_bij -> remove_top_not e
  | _      -> e

let rec build_obs ~trans ~glitch obs s c =
  match c with
  | [] -> ()
  | {instr_d = Imacro _} :: _ -> assert false
  | {instr_d = Iassgn i; instr_info = pp } :: c ->
    let e = subst_e s i.i_expr in
    let pp fmt () =
      pp fmt ();
      (* Format.fprintf fmt "(* from @[%a@] *)@ " (pp_expr ~full:dft_pinfo) e *) in
    let etrans =
      if trans then
        try Some (remove_top_not (expr_of_pexpr (E.Hv.find s i.i_var)))
        with Not_found -> None (* The variable has not been assigned before *)
      else None in
    let e =
      match i.i_kind with
      | P.IK_sub ->
        let e = add_sub obs e pp in
        add_trans obs etrans e pp;
        Ebox e
      | P.IK_glitch ->
        if glitch then
          begin
            add_glitch obs etrans e pp;
            let e = expr_of_pexpr e in
            Ebox e
          end
        else
          let e = add_sub obs e pp in
          add_trans obs etrans e pp;
          Ebox e
      | P.IK_hide ->
        let e = expr_of_pexpr e in
        add_observation obs e pp;
        Ebox e
      | P.IK_subst ->
        if glitch then
          begin
            add_glitch obs etrans e pp;
            e
          end
        else
          let e = add_sub obs e pp in
          add_trans obs etrans e pp;
          Ebox e
      | P.IK_noleak ->
        e
    in
    E.Hv.replace s i.i_var e;
    build_obs ~trans ~glitch obs s c
  |  {instr_d = Ileak l; instr_info = pp } :: c ->
    let e = List.map (subst_e s) l.l_exprs in
    let ees = List.map (expr_of_pexpr) e in
    let eea = Array.of_list ees in
    let e = E.tuple eea in
    add_observation obs e pp;
    build_obs ~trans ~glitch obs s c

let sub_array es1 es2 =
  let n1 = Array.length es1 in
  let n2 = Array.length es2 in
  if n2 < n1 then false
  else
    let rec aux i1 i2 =
      if i1 = n1 then true
      else if i2 = n2 then false
      else
        let cmp = E.E.compare es1.(i1) es2.(i2) in
        if cmp = 0 then aux (i1+1) (i2+1)
        else aux i1 (i2+1) in
    aux 0 0

let remove_subtuple pin obs =
  let pin = E.Se.of_list (List.map E.pub pin) in
  (* Remove public inputs *)
  let obs = E.Se.diff obs pin in
  (* Remove subtuple *)
  let obs = E.Se.elements obs in
(*  Format.printf "@[<v>possible observations:@ %a@]@."
    (pp_list "@ " E.pp_expr) obs; *)
  let cmp e1 e2 =
    match e1.E.e_node, e2.E.e_node with
    | E.Eop(_,o1,es1), E.Eop(_,o2,es2)
        when E.is_op_tuple o1 && E.is_op_tuple o2 ->
      Array.length es2 - Array.length es1
    | E.Eop(_,o1,_), _ when E.is_op_tuple o1 -> -1
    | _, E.Eop(_,o2,_) when E.is_op_tuple o2 -> 1
    | _, _ -> 0 in
  let obs = List.sort cmp obs in
  let tbl = E.He.create 107 in
  let robs = ref E.Se.empty in
  let add_singleton e = robs := E.Se.add e !robs in
  let add_tuple es =
    let add1 e =
      let rtuples =
        try E.He.find tbl e
        with Not_found ->
          let r = ref [] in E.He.add tbl e r; r in
      rtuples := es::!rtuples in
    Array.iter add1 es in
  let is_subtuple es1 tuples =
    List.exists (sub_array es1) tuples in
  let doit e =
    let es =
      match e.E.e_node with
      | E.Eop(_,o,es) when E.is_op_tuple o -> es
      | _ -> [|e|] in
    if Array.length es <> 0 then
      let e0 = es.(0) in
      let tuples =
        try !(E.He.find tbl e0)
        with Not_found -> [] in
      if not (is_subtuple es tuples) then begin
          add_singleton e;
          add_tuple es
        end
  in
  List.iter doit obs;
  E.Se.elements !robs

let build_obs_func ~ni ~trans ~glitch loc f =
  let nb_shares = ref 0 in
  let check_shares xs =
    let xs = Array.of_list xs in
    if !nb_shares = 0 then nb_shares := Array.length xs;
    if !nb_shares <> Array.length xs then
      error loc "not the same number of shares";
    xs in
  let s = E.Hv.create 101 in
  let obs = E.He.create 1007 in
  let add_subst x p = E.Hv.add s x (Ebox p) in
  let add_params (x, xs) =
    let xs = check_shares xs in
    let mk_param i xi =
      let p = E.share x i xi in
      let pp fmt () =
        Format.fprintf fmt "(* params %a *)@ " (pp_var ~full:dft_pinfo) xi in
      if ni <> `Threshold then
        ignore (add_observation obs p pp);
      add_subst xi p in
    Array.iteri mk_param xs;
    x
  in
  (* Build the parameters and the substitution *)
  let params = List.map add_params f.f_in in
  let add_vars s mk_e =
    let add x =
      let pp fmt () =
        Format.fprintf fmt "(* %s %a *)@ " s (pp_var ~full:dft_pinfo) x in
      let e = mk_e x in
      ignore (add_observation obs e pp);
      add_subst x e in
    List.iter add in
  (* Build the randoms *)
  add_vars "randoms" E.rnd f.f_rand;
  (* Build the public variables *)
  add_vars "public" E.pub f.f_pin;
  build_obs ~trans ~glitch obs s f.f_cmd;

  (* Add the observation on the output variables *)
  let add_out out =
    List.map (fun x ->
        let e = subst_v s x in
        let pp fmt () =
          Format.fprintf fmt "(* output %a *)@ "
            (pp_var ~full:dft_pinfo) x in
        let e =
          if glitch then glitch_expr None e
          else expr_of_pexpr e in
        add_observation obs e pp;
        e) out in
  let out = List.map add_out f.f_out in

  let all =
    E.He.fold (fun e _ interns -> E.Se.add e interns) obs E.Se.empty in
  let interns, out =
    match ni with
    | `Threshold -> all, []
    | `NI -> all, []
    | `SNI ->
      (* Compute the set of output *)
      let out = List.map E.Se.of_list out in
      let torm = List.fold_left E.Se.union E.Se.empty out  in
(*        match out with
        | [] -> [E.Se.empty]
        | [out] -> [E.Se.of_list out]
        | _ ->
          error loc
            "the function %a has more that one output, do not known how to check SNI"
            E.pp_var f.f_name in *)
      (* Remove out from the set of obs *)
      E.Se.diff all torm, List.map E.Se.elements out in
  (* We remove sub-tuples all projections of a tuples:
     i.e if (e1,e2,e3), e1, (e1,e3) are in the set we keep only (e1,e2,e3),
     since the adversary can directly observes (e1,e2,e3) to get e1 or (e1,e3)
   *)
  let pp_elems =
    verbose 2 "@[<v>%a@]@." (pp_list "@ " E.pp_expr) in

  verbose 1 "number of internal observations = %i@." (E.Se.cardinal interns);
  pp_elems (E.Se.elements interns);
  let interns = remove_subtuple f.f_pin interns in
  verbose 1 "after removing: number of internal observations = %i@."
    (List.length interns);
  pp_elems interns;
  let fout = List.flatten out in
  verbose 1 "number of output observations = %i@." (List.length fout);
  pp_elems fout;
  (* Now build the list of Checker.expr_info *)
  let pp_e pp e fmt () =
    pp fmt ();
    (* Format.fprintf fmt "@[%a@]@ " E.pp_expr e *) in
  let mk_ei e =
    { Checker.red_expr = e;
      Checker.pp_info =
        try pp_e (E.He.find obs e) e with Not_found ->
          Format.eprintf "no info for %a@." E.pp_expr e;
          assert false } in
  let interns = List.map mk_ei interns in
  let out     = List.map (List.map mk_ei) out in

  (params, !nb_shares, interns, out)


(* --------------------------------------------------------------- *)
let threshold func =
  let init = ref [] in
  let rnds = ref [] in
  let mk_rnd x =
    let r = E.V.clone x in
    rnds := r :: !rnds;
    let i = { i_var = x;
              i_kind = P.IK_subst;
              i_expr = Evar r } in
    let i = {
        instr_d = Iassgn i;
        instr_info = fun fmt () -> Format.fprintf fmt "(* initial random share *)@ "
      } in
    init := i :: !init;
    Evar x in
  let mk_shared x0 x es =
    let op = E.o_add x.E.v_ty in
    let i =
      {i_var = x0;
       i_kind = P.IK_hide;
       i_expr = List.fold_left (fun e1 e2 -> Eop2(op, e1, e2)) (Evar x) es} in
    let i = {
        instr_d = Iassgn i;
        instr_info = fun fmt () -> Format.fprintf fmt "(* sum share share *)@ "
      } in
    init := i :: !init in
  let init_input (x,xs) =
    match xs with
    | [] -> assert false
    | x0::xs ->
      let es = List.map mk_rnd xs in
      let x' = E.V.clone x in
      mk_shared x0 x' es;
      (x,[x']) in
  let f_in = List.map init_input func.f_in in
  { func with
    f_name = HS.make (func.f_name.hs_str ^ "_threshold");
    f_in;
    f_rand = List.rev_append !rnds func.f_rand;
    f_cmd  = List.rev_append !init func.f_cmd }
