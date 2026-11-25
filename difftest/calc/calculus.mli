
type __ = Obj.t

val negb : bool -> bool

val snd : ('a1 * 'a2) -> 'a2

val app : 'a1 list -> 'a1 list -> 'a1 list

module Nat :
 sig
 end

val map : ('a1 -> 'a2) -> 'a1 list -> 'a2 list

val seq : int -> int -> int list

val nth_error : 'a1 list -> int -> 'a1 option

val list_eq_dec : ('a1 -> 'a1 -> bool) -> 'a1 list -> 'a1 list -> bool

val flat_map : ('a1 -> 'a2 list) -> 'a1 list -> 'a2 list

val fold_right : ('a2 -> 'a1 -> 'a1) -> 'a1 -> 'a2 list -> 'a1

val existsb : ('a1 -> bool) -> 'a1 list -> bool

val filter : ('a1 -> bool) -> 'a1 list -> 'a1 list

type service =
  __ -> int -> __ -> ((__ * (__ -> __)) * __) option
  (* singleton inductive, whose constructor was Build_Service *)

type st = __

type op = __

type out = __

type ('k, 'c) prog =
| PDone
| PFail
| POp of 'k * op * (out -> ('k, 'c) prog)
| PProvide of 'k * st * ('k, 'c) prog
| PSpawn of 'c * ('k, 'c) prog

type ('k, 'c) component = { deps : 'k list; provs : 'k list;
                            body : ('k, 'c) prog; reacts : 'c list }

type err =
| EUser
| EOp
| EUnresolved
| EConflict

type 'k undo =
| UOp of 'k * int * int * (st -> st)
| UProv of 'k * int
| USpawn of int

type 'k view = ('k * int) list

type ('k, 'c) life =
| Inactive of err option
| Loading of ('k, 'c) prog * 'k undo list * 'k view
| Active of 'k undo list * 'k view
| Unloading of 'k undo list * 'k view * err option

type ('k, 'c) fiber = { comp : 'c; parent : int option; disposed : bool;
                        life0 : ('k, 'c) life }

val comp : service -> ('a1, 'a2) fiber -> 'a2

val parent : service -> ('a1, 'a2) fiber -> int option

val disposed : service -> ('a1, 'a2) fiber -> bool

val life0 : service -> ('a1, 'a2) fiber -> ('a1, 'a2) life

type binding = { pid : int; owner : int; bst : st }

val pid : service -> binding -> int

val owner : service -> binding -> int

val bst : service -> binding -> st

type ('k, 'c) state = { next : int; fibers : (int -> ('k, 'c) fiber option);
                        binds : ('k -> binding option);
                        oplog : (int -> op option);
                        inilog : (int -> st option) }

val next : service -> ('a1, 'a2) state -> int

val fibers : service -> ('a1, 'a2) state -> int -> ('a1, 'a2) fiber option

val binds : service -> ('a1, 'a2) state -> 'a1 -> binding option

val init : service -> ('a1, 'a2) state

val keqb : ('a1 -> 'a1 -> bool) -> 'a1 -> 'a1 -> bool

val kmem : ('a1 -> 'a1 -> bool) -> 'a1 -> 'a1 list -> bool

val overlaps : ('a1 -> 'a1 -> bool) -> 'a1 list -> 'a1 list -> bool

val fupd :
  service -> (int -> ('a1, 'a2) fiber option) -> int -> ('a1, 'a2) fiber
  option -> int -> ('a1, 'a2) fiber option

val bupd :
  ('a1 -> 'a1 -> bool) -> service -> ('a1 -> binding option) -> 'a1 ->
  binding option -> 'a1 -> binding option

val names : service -> ('a1, 'a2) state -> int list

val is_active : service -> ('a1, 'a2) life -> bool

val is_installed : service -> ('a1, 'a2) life -> bool

val view_of : service -> ('a1, 'a2) life -> 'a1 view

val view_eq_dec : ('a1 -> 'a1 -> bool) -> 'a1 view -> 'a1 view -> bool

val lookup_view : ('a1 -> 'a1 -> bool) -> 'a1 -> 'a1 view -> int option

val visible : service -> ('a1, 'a2) state -> 'a1 -> int option

val resolve : service -> ('a1, 'a2) state -> 'a1 list -> 'a1 view option

val target :
  service -> ('a2 -> ('a1, 'a2) component) -> ('a1, 'a2) state -> int -> 'a1
  view option

val target_is :
  ('a1 -> 'a1 -> bool) -> service -> ('a2 -> ('a1, 'a2) component) -> ('a1,
  'a2) state -> int -> 'a1 view -> bool

val may_step :
  ('a1 -> 'a1 -> bool) -> service -> ('a2 -> ('a1, 'a2) component) -> ('a1,
  'a2) state -> int -> ('a1, 'a2) prog -> 'a1 view -> bool

val resolves : service -> ('a1, 'a2) state -> int -> int -> bool

val relied : service -> ('a1, 'a2) state -> int -> int -> bool

val held : service -> ('a1, 'a2) state -> int -> 'a1 undo list -> bool

val has_child : service -> ('a1, 'a2) state -> int -> bool

val conflict :
  ('a1 -> 'a1 -> bool) -> service -> ('a2 -> ('a1, 'a2) component) -> ('a1,
  'a2) state -> 'a2 -> bool

val with_fibers :
  service -> ('a1, 'a2) state -> (int -> ('a1, 'a2) fiber option) -> ('a1,
  'a2) state

val with_binds :
  service -> ('a1, 'a2) state -> ('a1 -> binding option) -> ('a1, 'a2) state

val bump : service -> ('a1, 'a2) state -> ('a1, 'a2) state

val log_op : service -> ('a1, 'a2) state -> int -> op -> ('a1, 'a2) state

val log_ini : service -> ('a1, 'a2) state -> int -> st -> ('a1, 'a2) state

val set_fiber :
  service -> ('a1, 'a2) state -> int -> ('a1, 'a2) fiber -> ('a1, 'a2) state

val set_life :
  service -> ('a1, 'a2) state -> int -> ('a1, 'a2) fiber -> ('a1, 'a2) life
  -> ('a1, 'a2) state

type 'c label =
| OInsert of 'c
| ODispose of int
| OReset of int
| LBegin of int
| LStep of int
| LDivert of int
| LLeave of int
| LUndo of int
| LRetireChild of int
| LUnloaded of int
| LRemove of int
| OReact of int * int
| ORestart of int

val load_step :
  ('a1 -> 'a1 -> bool) -> service -> ('a2 -> ('a1, 'a2) component) -> ('a1,
  'a2) state -> int -> ('a1, 'a2) fiber -> ('a1, 'a2) prog -> 'a1 undo list
  -> 'a1 view -> ('a1, 'a2) state

val undo_step :
  ('a1 -> 'a1 -> bool) -> service -> ('a1, 'a2) state -> int -> ('a1, 'a2)
  fiber -> 'a1 undo -> 'a1 undo list -> 'a1 view -> err option -> ('a1, 'a2)
  state option

val step :
  ('a1 -> 'a1 -> bool) -> service -> ('a2 -> ('a1, 'a2) component) -> ('a1,
  'a2) state -> 'a2 label -> ('a1, 'a2) state option

val lifecycle_labels : int -> 'a1 label list

type ('name, 'v) rSt = 'name -> 'v option

type ('name, 'v) rOp =
| Register of 'name * 'v
| Lookup of 'name

val upd :
  ('a1 -> 'a1 -> bool) -> ('a1, 'a2) rSt -> 'a1 -> 'a2 option -> ('a1, 'a2)
  rSt

val rrun :
  ('a1 -> 'a1 -> bool) -> ('a1, 'a2) rOp -> int -> ('a1, 'a2) rSt -> ((('a1,
  'a2) rSt * (('a1, 'a2) rSt -> ('a1, 'a2) rSt)) * 'a2 option) option

val registry : ('a1 -> 'a1 -> bool) -> service

val _UU03a3_R : service

type dComp = (int, int) component

type dProg = (int, int) prog

type dState = (int, int) state

type dLabel = int label

val dinit : dState

val dstep : (int -> dComp) -> dState -> dLabel -> dState option

val denabled : (int -> dComp) -> dState -> dLabel list

val dop : int -> int -> int -> dProg -> dProg

val dprovide : int -> (int * int) list -> dProg -> dProg

val dspawn : int -> dProg -> dProg

val ddone : dProg

val dfail : dProg

val dcomp : int list -> int list -> dProg -> dComp

val dop_name : dState -> int -> int option

val dbinding : dState -> int -> int list -> (int * int option list) option

val dinstr : dProg -> int * int list
