module List :
  sig
    val length : 'a list -> int
    val hd : 'a list -> 'a
    val tl : 'a list -> 'a list
    val nth : 'a list -> int -> 'a
    val rev : 'a list -> 'a list
    val append : 'a list -> 'a list -> 'a list
    val rev_append : 'a list -> 'a list -> 'a list
    val concat : 'a list list -> 'a list
    val flatten : 'a list list -> 'a list
    val iter : ('a -> unit) -> 'a list -> unit
    val iteri : (int -> 'a -> unit) -> 'a list -> unit
    val map : ('a -> 'b) -> 'a list -> 'b list
    val mapi : (int -> 'a -> 'b) -> 'a list -> 'b list
    val rev_map : ('a -> 'b) -> 'a list -> 'b list
    val fold_left : ('a -> 'b -> 'a) -> 'a -> 'b list -> 'a
    val fold_right : ('a -> 'b -> 'b) -> 'a list -> 'b -> 'b
    val iter2 : ('a -> 'b -> unit) -> 'a list -> 'b list -> unit
    val map2 : ('a -> 'b -> 'c) -> 'a list -> 'b list -> 'c list
    val rev_map2 : ('a -> 'b -> 'c) -> 'a list -> 'b list -> 'c list
    val fold_left2 : ('a -> 'b -> 'c -> 'a) -> 'a -> 'b list -> 'c list -> 'a
    val fold_right2 :
      ('a -> 'b -> 'c -> 'c) -> 'a list -> 'b list -> 'c -> 'c
    val for_all : ('a -> bool) -> 'a list -> bool
    val exists : ('a -> bool) -> 'a list -> bool
    val for_all2 : ('a -> 'b -> bool) -> 'a list -> 'b list -> bool
    val exists2 : ('a -> 'b -> bool) -> 'a list -> 'b list -> bool
    val mem : 'a -> 'a list -> bool
    val memq : 'a -> 'a list -> bool
    val find : ('a -> bool) -> 'a list -> 'a
    val filter : ('a -> bool) -> 'a list -> 'a list
    val find_all : ('a -> bool) -> 'a list -> 'a list
    val partition : ('a -> bool) -> 'a list -> 'a list * 'a list
    val assoc : 'a -> ('a * 'b) list -> 'b
    val assq : 'a -> ('a * 'b) list -> 'b
    val mem_assoc : 'a -> ('a * 'b) list -> bool
    val mem_assq : 'a -> ('a * 'b) list -> bool
    val remove_assoc : 'a -> ('a * 'b) list -> ('a * 'b) list
    val remove_assq : 'a -> ('a * 'b) list -> ('a * 'b) list
    val split : ('a * 'b) list -> 'a list * 'b list
    val combine : 'a list -> 'b list -> ('a * 'b) list
    val sort : ('a -> 'a -> int) -> 'a list -> 'a list
    val stable_sort : ('a -> 'a -> int) -> 'a list -> 'a list
    val fast_sort : ('a -> 'a -> int) -> 'a list -> 'a list
    val sort_uniq : ('a -> 'a -> int) -> 'a list -> 'a list
    val merge : ('a -> 'a -> int) -> 'a list -> 'a list -> 'a list
    val count : ('a -> bool) -> 'a list -> int
    val map_size : ('a -> 'b) -> 'a list -> 'b list * int
    val is_empty : 'a list -> bool
  end

(* ----------------------------------------------------------------------- *)

val partition :
  ('a -> bool) -> 'a list -> 'a list -> 'a list -> 'a list * 'a list

val pp_list :
  ('a, 'b, 'c, 'd, 'd, 'a) CamlinternalFormatBasics.format6 ->
  (Format.formatter -> 'e -> unit) -> Format.formatter -> 'e list -> unit

(* ----------------------------------------------------------------------- *)

module Mint : Map.S with type key = int
module Mstr : Map.S with type key = string

(* ----------------------------------------------------------------------- *)
module Array :
  sig
    external length : 'a array -> int = "%array_length"
    external get : 'a array -> int -> 'a = "%array_safe_get"
    external set : 'a array -> int -> 'a -> unit = "%array_safe_set"
    external make : int -> 'a -> 'a array = "caml_make_vect"
    external create : int -> 'a -> 'a array = "caml_make_vect"
    val init : int -> (int -> 'a) -> 'a array
    val make_matrix : int -> int -> 'a -> 'a array array
    val create_matrix : int -> int -> 'a -> 'a array array
    val append : 'a array -> 'a array -> 'a array
    val concat : 'a array list -> 'a array
    val sub : 'a array -> int -> int -> 'a array
    val copy : 'a array -> 'a array
    val fill : 'a array -> int -> int -> 'a -> unit
    val blit : 'a array -> int -> 'a array -> int -> int -> unit
    val to_list : 'a array -> 'a list
    val of_list : 'a list -> 'a array
    val iter : ('a -> unit) -> 'a array -> unit
    val map : ('a -> 'b) -> 'a array -> 'b array
    val iteri : (int -> 'a -> unit) -> 'a array -> unit
    val mapi : (int -> 'a -> 'b) -> 'a array -> 'b array
    val fold_left : ('a -> 'b -> 'a) -> 'a -> 'b array -> 'a
    val fold_right : ('b -> 'a -> 'a) -> 'b array -> 'a -> 'a
    external make_float : int -> float array = "caml_make_float_vect"
    val sort : ('a -> 'a -> int) -> 'a array -> unit
    val stable_sort : ('a -> 'a -> int) -> 'a array -> unit
    val fast_sort : ('a -> 'a -> int) -> 'a array -> unit
    external unsafe_get : 'a array -> int -> 'a = "%array_unsafe_get"
    external unsafe_set : 'a array -> int -> 'a -> unit = "%array_unsafe_set"
    val for_all : ('a -> bool) -> 'a array -> bool
  end

(* ----------------------------------------------------------------------- *)

exception EmptyStack
module Stack : 
  sig 
    type 'a t
    val make : int  -> 'a -> 'a t
    val push : 'a t -> 'a -> unit
    val pop  : 'a t -> 'a 
    val clear: 'a t -> unit 

    val to_list : 'a t -> 'a list
    val iter : ('a -> unit) -> 'a t -> unit
  end
      

(* ----------------------------------------------------------------------- *)
val finally : (unit -> 'a) -> ('b -> 'c) -> 'b -> 'c

(* ----------------------------------------------------------------------- *)
module Vector : sig 

  type 'a t 
  val dummy  : unit -> 'a t
  val create : int -> 'a -> 'a t
  val clear  : 'a t -> unit 
  val push   : 'a t -> 'a -> unit
  val size   : 'a t -> int
  val pop    : 'a t -> 'a 
  val top    : 'a t -> 'a

  (* remove all elements satisfying the predicate *)
  val remove : ('a -> bool) -> 'a t -> unit

  val iter   : ('a -> unit) -> 'a t -> unit
  val exists : ('a -> bool) -> 'a t -> bool

  val to_list : 'a t -> 'a list                                       
end
