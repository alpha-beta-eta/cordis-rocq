
type __ = Obj.t

(** val negb : bool -> bool **)

let negb = function
| true -> false
| false -> true

(** val snd : ('a1 * 'a2) -> 'a2 **)

let snd = function
| (_, y) -> y

(** val app : 'a1 list -> 'a1 list -> 'a1 list **)

let rec app l m =
  match l with
  | [] -> m
  | a :: l1 -> a :: (app l1 m)

module Nat =
 struct
 end

(** val map : ('a1 -> 'a2) -> 'a1 list -> 'a2 list **)

let rec map f = function
| [] -> []
| a :: l0 -> (f a) :: (map f l0)

(** val seq : int -> int -> int list **)

let rec seq start len =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> [])
    (fun len0 -> start :: (seq (Stdlib.Int.succ start) len0))
    len

(** val nth_error : 'a1 list -> int -> 'a1 option **)

let rec nth_error l n =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> match l with
              | [] -> None
              | x :: _ -> Some x)
    (fun n0 -> match l with
               | [] -> None
               | _ :: l' -> nth_error l' n0)
    n

(** val list_eq_dec : ('a1 -> 'a1 -> bool) -> 'a1 list -> 'a1 list -> bool **)

let rec list_eq_dec eq_dec l l' =
  match l with
  | [] -> (match l' with
           | [] -> true
           | _ :: _ -> false)
  | y :: l0 ->
    (match l' with
     | [] -> false
     | a :: l1 -> if eq_dec y a then list_eq_dec eq_dec l0 l1 else false)

(** val flat_map : ('a1 -> 'a2 list) -> 'a1 list -> 'a2 list **)

let rec flat_map f = function
| [] -> []
| x :: l0 -> app (f x) (flat_map f l0)

(** val fold_right : ('a2 -> 'a1 -> 'a1) -> 'a1 -> 'a2 list -> 'a1 **)

let rec fold_right f a0 = function
| [] -> a0
| b :: l0 -> f b (fold_right f a0 l0)

(** val existsb : ('a1 -> bool) -> 'a1 list -> bool **)

let rec existsb f = function
| [] -> false
| a :: l0 -> (||) (f a) (existsb f l0)

(** val filter : ('a1 -> bool) -> 'a1 list -> 'a1 list **)

let rec filter f = function
| [] -> []
| x :: l0 -> if f x then x :: (filter f l0) else filter f l0

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

(** val comp : service -> ('a1, 'a2) fiber -> 'a2 **)

let comp _ f =
  f.comp

(** val parent : service -> ('a1, 'a2) fiber -> int option **)

let parent _ f =
  f.parent

(** val disposed : service -> ('a1, 'a2) fiber -> bool **)

let disposed _ f =
  f.disposed

(** val life0 : service -> ('a1, 'a2) fiber -> ('a1, 'a2) life **)

let life0 _ f =
  f.life0

type binding = { pid : int; owner : int; bst : st }

(** val pid : service -> binding -> int **)

let pid _ b =
  b.pid

(** val owner : service -> binding -> int **)

let owner _ b =
  b.owner

(** val bst : service -> binding -> st **)

let bst _ b =
  b.bst

type ('k, 'c) state = { next : int; fibers : (int -> ('k, 'c) fiber option);
                        binds : ('k -> binding option);
                        oplog : (int -> op option);
                        inilog : (int -> st option) }

(** val next : service -> ('a1, 'a2) state -> int **)

let next _ s =
  s.next

(** val fibers :
    service -> ('a1, 'a2) state -> int -> ('a1, 'a2) fiber option **)

let fibers _ s =
  s.fibers

(** val binds : service -> ('a1, 'a2) state -> 'a1 -> binding option **)

let binds _ s =
  s.binds

(** val init : service -> ('a1, 'a2) state **)

let init _ =
  { next = 0; fibers = (fun _ -> None); binds = (fun _ -> None); oplog =
    (fun _ -> None); inilog = (fun _ -> None) }

(** val keqb : ('a1 -> 'a1 -> bool) -> 'a1 -> 'a1 -> bool **)

let keqb k_eq_dec x y =
  if k_eq_dec x y then true else false

(** val kmem : ('a1 -> 'a1 -> bool) -> 'a1 -> 'a1 list -> bool **)

let kmem k_eq_dec k ks =
  existsb (keqb k_eq_dec k) ks

(** val overlaps : ('a1 -> 'a1 -> bool) -> 'a1 list -> 'a1 list -> bool **)

let overlaps k_eq_dec ks1 ks2 =
  existsb (fun k -> kmem k_eq_dec k ks2) ks1

(** val fupd :
    service -> (int -> ('a1, 'a2) fiber option) -> int -> ('a1, 'a2) fiber
    option -> int -> ('a1, 'a2) fiber option **)

let fupd _ f n o m =
  if (=) m n then o else f m

(** val bupd :
    ('a1 -> 'a1 -> bool) -> service -> ('a1 -> binding option) -> 'a1 ->
    binding option -> 'a1 -> binding option **)

let bupd k_eq_dec _ b k o k' =
  if keqb k_eq_dec k' k then o else b k'

(** val names : service -> ('a1, 'a2) state -> int list **)

let names _ _UU03b3_ =
  seq 0 _UU03b3_.next

(** val is_active : service -> ('a1, 'a2) life -> bool **)

let is_active _ = function
| Active (_, _) -> true
| _ -> false

(** val is_installed : service -> ('a1, 'a2) life -> bool **)

let is_installed _ = function
| Inactive _ -> false
| _ -> true

(** val view_of : service -> ('a1, 'a2) life -> 'a1 view **)

let view_of _ = function
| Inactive _ -> []
| Loading (_, _, w) -> w
| Active (_, w) -> w
| Unloading (_, w, _) -> w

(** val view_eq_dec : ('a1 -> 'a1 -> bool) -> 'a1 view -> 'a1 view -> bool **)

let view_eq_dec k_eq_dec =
  list_eq_dec (fun x y ->
    let (k, n) = x in
    let (k0, n0) = y in let s = k_eq_dec k k0 in if s then (=) n n0 else false)

(** val lookup_view :
    ('a1 -> 'a1 -> bool) -> 'a1 -> 'a1 view -> int option **)

let rec lookup_view k_eq_dec k = function
| [] -> None
| p0 :: w' ->
  let (k', p) = p0 in
  if keqb k_eq_dec k k' then Some p else lookup_view k_eq_dec k w'

(** val visible : service -> ('a1, 'a2) state -> 'a1 -> int option **)

let visible _UU03a3_ _UU03b3_ k =
  match _UU03b3_.binds k with
  | Some b ->
    (match _UU03b3_.fibers b.owner with
     | Some f -> if is_active _UU03a3_ f.life0 then Some b.pid else None
     | None -> None)
  | None -> None

(** val resolve :
    service -> ('a1, 'a2) state -> 'a1 list -> 'a1 view option **)

let rec resolve _UU03a3_ _UU03b3_ = function
| [] -> Some []
| k :: ks' ->
  (match visible _UU03a3_ _UU03b3_ k with
   | Some p ->
     (match resolve _UU03a3_ _UU03b3_ ks' with
      | Some w -> Some ((k, p) :: w)
      | None -> None)
   | None -> None)

(** val target :
    service -> ('a2 -> ('a1, 'a2) component) -> ('a1, 'a2) state -> int ->
    'a1 view option **)

let target _UU03a3_ prog0 _UU03b3_ n =
  match _UU03b3_.fibers n with
  | Some f ->
    if f.disposed then None else resolve _UU03a3_ _UU03b3_ (prog0 f.comp).deps
  | None -> None

(** val target_is :
    ('a1 -> 'a1 -> bool) -> service -> ('a2 -> ('a1, 'a2) component) -> ('a1,
    'a2) state -> int -> 'a1 view -> bool **)

let target_is k_eq_dec _UU03a3_ prog0 _UU03b3_ n w =
  match target _UU03a3_ prog0 _UU03b3_ n with
  | Some w' -> if view_eq_dec k_eq_dec w w' then true else false
  | None -> false

(** val may_step :
    ('a1 -> 'a1 -> bool) -> service -> ('a2 -> ('a1, 'a2) component) -> ('a1,
    'a2) state -> int -> ('a1, 'a2) prog -> 'a1 view -> bool **)

let may_step k_eq_dec _UU03a3_ prog0 _UU03b3_ n p w =
  match p with
  | PDone -> target_is k_eq_dec _UU03a3_ prog0 _UU03b3_ n w
  | _ -> true

(** val resolves : service -> ('a1, 'a2) state -> int -> int -> bool **)

let resolves _UU03a3_ _UU03b3_ m p =
  match _UU03b3_.fibers m with
  | Some f ->
    (&&) (is_installed _UU03a3_ f.life0)
      (existsb (fun kp -> (=) (snd kp) p) (view_of _UU03a3_ f.life0))
  | None -> false

(** val relied : service -> ('a1, 'a2) state -> int -> int -> bool **)

let relied _UU03a3_ _UU03b3_ n p =
  existsb (fun m -> (&&) (negb ((=) m n)) (resolves _UU03a3_ _UU03b3_ m p))
    (names _UU03a3_ _UU03b3_)

(** val held : service -> ('a1, 'a2) state -> int -> 'a1 undo list -> bool **)

let held _UU03a3_ _UU03b3_ n acc =
  existsb (fun u ->
    match u with
    | UProv (_, p) -> relied _UU03a3_ _UU03b3_ n p
    | _ -> false) acc

(** val has_child : service -> ('a1, 'a2) state -> int -> bool **)

let has_child _UU03a3_ _UU03b3_ n =
  existsb (fun m ->
    match _UU03b3_.fibers m with
    | Some f -> (match f.parent with
                 | Some q -> (=) q n
                 | None -> false)
    | None -> false) (names _UU03a3_ _UU03b3_)

(** val conflict :
    ('a1 -> 'a1 -> bool) -> service -> ('a2 -> ('a1, 'a2) component) -> ('a1,
    'a2) state -> 'a2 -> bool **)

let conflict k_eq_dec _UU03a3_ prog0 _UU03b3_ c =
  existsb (fun m ->
    match _UU03b3_.fibers m with
    | Some f -> overlaps k_eq_dec (prog0 c).provs (prog0 f.comp).provs
    | None -> false) (names _UU03a3_ _UU03b3_)

(** val with_fibers :
    service -> ('a1, 'a2) state -> (int -> ('a1, 'a2) fiber option) -> ('a1,
    'a2) state **)

let with_fibers _ _UU03b3_ f =
  { next = _UU03b3_.next; fibers = f; binds = _UU03b3_.binds; oplog =
    _UU03b3_.oplog; inilog = _UU03b3_.inilog }

(** val with_binds :
    service -> ('a1, 'a2) state -> ('a1 -> binding option) -> ('a1, 'a2) state **)

let with_binds _ _UU03b3_ b =
  { next = _UU03b3_.next; fibers = _UU03b3_.fibers; binds = b; oplog =
    _UU03b3_.oplog; inilog = _UU03b3_.inilog }

(** val bump : service -> ('a1, 'a2) state -> ('a1, 'a2) state **)

let bump _ _UU03b3_ =
  { next = (Stdlib.Int.succ _UU03b3_.next); fibers = _UU03b3_.fibers; binds =
    _UU03b3_.binds; oplog = _UU03b3_.oplog; inilog = _UU03b3_.inilog }

(** val log_op :
    service -> ('a1, 'a2) state -> int -> op -> ('a1, 'a2) state **)

let log_op _ _UU03b3_ t a =
  { next = _UU03b3_.next; fibers = _UU03b3_.fibers; binds = _UU03b3_.binds;
    oplog = (fun t' -> if (=) t' t then Some a else _UU03b3_.oplog t');
    inilog = _UU03b3_.inilog }

(** val log_ini :
    service -> ('a1, 'a2) state -> int -> st -> ('a1, 'a2) state **)

let log_ini _ _UU03b3_ p s =
  { next = _UU03b3_.next; fibers = _UU03b3_.fibers; binds = _UU03b3_.binds;
    oplog = _UU03b3_.oplog; inilog = (fun p' ->
    if (=) p' p then Some s else _UU03b3_.inilog p') }

(** val set_fiber :
    service -> ('a1, 'a2) state -> int -> ('a1, 'a2) fiber -> ('a1, 'a2) state **)

let set_fiber _UU03a3_ _UU03b3_ n f =
  with_fibers _UU03a3_ _UU03b3_ (fupd _UU03a3_ _UU03b3_.fibers n (Some f))

(** val set_life :
    service -> ('a1, 'a2) state -> int -> ('a1, 'a2) fiber -> ('a1, 'a2) life
    -> ('a1, 'a2) state **)

let set_life _UU03a3_ _UU03b3_ n f l =
  set_fiber _UU03a3_ _UU03b3_ n { comp = f.comp; parent = f.parent;
    disposed = f.disposed; life0 = l }

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

(** val load_step :
    ('a1 -> 'a1 -> bool) -> service -> ('a2 -> ('a1, 'a2) component) -> ('a1,
    'a2) state -> int -> ('a1, 'a2) fiber -> ('a1, 'a2) prog -> 'a1 undo list
    -> 'a1 view -> ('a1, 'a2) state **)

let load_step k_eq_dec _UU03a3_ prog0 _UU03b3_ n f p acc w =
  let fail = fun z ->
    set_life _UU03a3_ _UU03b3_ n f (Unloading (acc, w, (Some z)))
  in
  (match p with
   | PDone -> set_life _UU03a3_ _UU03b3_ n f (Active (acc, w))
   | PFail -> fail EUser
   | POp (k, a, _UU03ba_) ->
     let rp =
       if kmem k_eq_dec k (prog0 f.comp).deps
       then lookup_view k_eq_dec k w
       else (match _UU03b3_.binds k with
             | Some b -> if (=) b.owner n then Some b.pid else None
             | None -> None)
     in
     (match rp with
      | Some p0 ->
        (match _UU03b3_.binds k with
         | Some b ->
           if (=) b.pid p0
           then (match _UU03a3_ a _UU03b3_.next b.bst with
                 | Some p1 ->
                   let (p2, o) = p1 in
                   let (s', g) = p2 in
                   let _UU03b3_1 =
                     bump _UU03a3_
                       (log_op _UU03a3_
                         (with_binds _UU03a3_ _UU03b3_
                           (bupd k_eq_dec _UU03a3_ _UU03b3_.binds k (Some
                             { pid = b.pid; owner = b.owner; bst = s' })))
                         _UU03b3_.next a)
                   in
                   set_life _UU03a3_ _UU03b3_1 n f (Loading ((_UU03ba_ o),
                     ((UOp (k, p0, _UU03b3_.next, g)) :: acc), w))
                 | None ->
                   set_life _UU03a3_ (bump _UU03a3_ _UU03b3_) n f (Unloading
                     (acc, w, (Some EOp))))
           else fail EUnresolved
         | None -> fail EUnresolved)
      | None -> fail EUnresolved)
   | PProvide (k, s, p') ->
     if kmem k_eq_dec k (prog0 f.comp).provs
     then (match _UU03b3_.binds k with
           | Some _ -> fail EConflict
           | None ->
             let p0 = _UU03b3_.next in
             let _UU03b3_1 =
               bump _UU03a3_
                 (log_ini _UU03a3_
                   (with_binds _UU03a3_ _UU03b3_
                     (bupd k_eq_dec _UU03a3_ _UU03b3_.binds k (Some { pid =
                       p0; owner = n; bst = s })))
                   p0 s)
             in
             set_life _UU03a3_ _UU03b3_1 n f (Loading (p', ((UProv (k,
               p0)) :: acc), w)))
     else fail EConflict
   | PSpawn (c, p') ->
     if conflict k_eq_dec _UU03a3_ prog0 _UU03b3_ c
     then fail EConflict
     else let m = _UU03b3_.next in
          let _UU03b3_1 =
            bump _UU03a3_
              (with_fibers _UU03a3_ _UU03b3_
                (fupd _UU03a3_ _UU03b3_.fibers m (Some { comp = c; parent =
                  (Some n); disposed = false; life0 = (Inactive None) })))
          in
          set_life _UU03a3_ _UU03b3_1 n f (Loading (p', ((USpawn m) :: acc),
            w)))

(** val undo_step :
    ('a1 -> 'a1 -> bool) -> service -> ('a1, 'a2) state -> int -> ('a1, 'a2)
    fiber -> 'a1 undo -> 'a1 undo list -> 'a1 view -> err option -> ('a1,
    'a2) state option **)

let undo_step k_eq_dec _UU03a3_ _UU03b3_ n f u acc w z =
  let continue = fun _UU03b3_' -> Some
    (set_life _UU03a3_ _UU03b3_' n f (Unloading (acc, w, z)))
  in
  (match u with
   | UOp (k, p, _, g) ->
     (match _UU03b3_.binds k with
      | Some b ->
        if (=) b.pid p
        then continue
               (with_binds _UU03a3_ _UU03b3_
                 (bupd k_eq_dec _UU03a3_ _UU03b3_.binds k (Some { pid =
                   b.pid; owner = b.owner; bst = (g b.bst) })))
        else continue _UU03b3_
      | None -> continue _UU03b3_)
   | UProv (k, p) ->
     if relied _UU03a3_ _UU03b3_ n p
     then None
     else (match _UU03b3_.binds k with
           | Some b ->
             if (=) b.pid p
             then continue
                    (with_binds _UU03a3_ _UU03b3_
                      (bupd k_eq_dec _UU03a3_ _UU03b3_.binds k None))
             else continue _UU03b3_
           | None -> continue _UU03b3_)
   | USpawn m ->
     (match _UU03b3_.fibers m with
      | Some _ -> None
      | None -> continue _UU03b3_))

(** val step :
    ('a1 -> 'a1 -> bool) -> service -> ('a2 -> ('a1, 'a2) component) -> ('a1,
    'a2) state -> 'a2 label -> ('a1, 'a2) state option **)

let step k_eq_dec _UU03a3_ prog0 _UU03b3_ = function
| OInsert c ->
  if conflict k_eq_dec _UU03a3_ prog0 _UU03b3_ c
  then None
  else Some
         (bump _UU03a3_
           (with_fibers _UU03a3_ _UU03b3_
             (fupd _UU03a3_ _UU03b3_.fibers _UU03b3_.next (Some { comp = c;
               parent = None; disposed = false; life0 = (Inactive None) }))))
| ODispose n ->
  (match _UU03b3_.fibers n with
   | Some f ->
     Some
       (set_fiber _UU03a3_ _UU03b3_ n { comp = f.comp; parent = f.parent;
         disposed = true; life0 = f.life0 })
   | None -> None)
| OReset n ->
  (match _UU03b3_.fibers n with
   | Some f ->
     (match f.life0 with
      | Inactive z ->
        (match z with
         | Some _ -> Some (set_life _UU03a3_ _UU03b3_ n f (Inactive None))
         | None -> None)
      | _ -> None)
   | None -> None)
| LBegin n ->
  (match _UU03b3_.fibers n with
   | Some f ->
     (match f.life0 with
      | Inactive z ->
        (match z with
         | Some _ -> None
         | None ->
           (match target _UU03a3_ prog0 _UU03b3_ n with
            | Some w ->
              Some
                (set_life _UU03a3_ _UU03b3_ n f (Loading
                  ((prog0 f.comp).body, [], w)))
            | None -> None))
      | _ -> None)
   | None -> None)
| LStep n ->
  (match _UU03b3_.fibers n with
   | Some f ->
     (match f.life0 with
      | Loading (p, acc, w) ->
        if may_step k_eq_dec _UU03a3_ prog0 _UU03b3_ n p w
        then Some (load_step k_eq_dec _UU03a3_ prog0 _UU03b3_ n f p acc w)
        else None
      | _ -> None)
   | None -> None)
| LDivert n ->
  (match _UU03b3_.fibers n with
   | Some f ->
     (match f.life0 with
      | Loading (_, acc, w) ->
        if target_is k_eq_dec _UU03a3_ prog0 _UU03b3_ n w
        then None
        else Some (set_life _UU03a3_ _UU03b3_ n f (Unloading (acc, w, None)))
      | _ -> None)
   | None -> None)
| LLeave n ->
  (match _UU03b3_.fibers n with
   | Some f ->
     (match f.life0 with
      | Active (acc, w) ->
        if target_is k_eq_dec _UU03a3_ prog0 _UU03b3_ n w
        then None
        else Some (set_life _UU03a3_ _UU03b3_ n f (Unloading (acc, w, None)))
      | _ -> None)
   | None -> None)
| LUndo n ->
  (match _UU03b3_.fibers n with
   | Some f ->
     (match f.life0 with
      | Unloading (acc0, w, z) ->
        (match acc0 with
         | [] -> None
         | u :: acc ->
           if held _UU03a3_ _UU03b3_ n (u :: acc)
           then None
           else undo_step k_eq_dec _UU03a3_ _UU03b3_ n f u acc w z)
      | _ -> None)
   | None -> None)
| LRetireChild n ->
  (match _UU03b3_.fibers n with
   | Some f ->
     (match f.life0 with
      | Unloading (acc0, _, _) ->
        (match acc0 with
         | [] -> None
         | u :: acc ->
           (match u with
            | USpawn m ->
              (match _UU03b3_.fibers m with
               | Some g ->
                 if (||) (held _UU03a3_ _UU03b3_ n ((USpawn m) :: acc))
                      g.disposed
                 then None
                 else Some
                        (set_fiber _UU03a3_ _UU03b3_ m { comp = g.comp;
                          parent = g.parent; disposed = true; life0 =
                          g.life0 })
               | None -> None)
            | _ -> None))
      | _ -> None)
   | None -> None)
| LUnloaded n ->
  (match _UU03b3_.fibers n with
   | Some f ->
     (match f.life0 with
      | Unloading (acc, _, z) ->
        (match acc with
         | [] -> Some (set_life _UU03a3_ _UU03b3_ n f (Inactive z))
         | _ :: _ -> None)
      | _ -> None)
   | None -> None)
| LRemove n ->
  (match _UU03b3_.fibers n with
   | Some f ->
     (match f.life0 with
      | Inactive _ ->
        if (&&) f.disposed (negb (has_child _UU03a3_ _UU03b3_ n))
        then Some
               (with_fibers _UU03a3_ _UU03b3_
                 (fupd _UU03a3_ _UU03b3_.fibers n None))
        else None
      | _ -> None)
   | None -> None)
| OReact (n, i) ->
  (match _UU03b3_.fibers n with
   | Some f ->
     (match f.life0 with
      | Active (acc, w) ->
        (match nth_error (prog0 f.comp).reacts i with
         | Some c ->
           if (||) f.disposed (conflict k_eq_dec _UU03a3_ prog0 _UU03b3_ c)
           then None
           else let m = _UU03b3_.next in
                let _UU03b3_1 =
                  bump _UU03a3_
                    (with_fibers _UU03a3_ _UU03b3_
                      (fupd _UU03a3_ _UU03b3_.fibers m (Some { comp = c;
                        parent = (Some n); disposed = false; life0 =
                        (Inactive None) })))
                in
                Some
                (set_life _UU03a3_ _UU03b3_1 n f (Active (((USpawn
                  m) :: acc), w)))
         | None -> None)
      | _ -> None)
   | None -> None)
| ORestart n ->
  (match _UU03b3_.fibers n with
   | Some f ->
     if f.disposed
     then None
     else (match f.life0 with
           | Loading (_, acc, w) ->
             Some (set_life _UU03a3_ _UU03b3_ n f (Unloading (acc, w, None)))
           | Active (acc, w) ->
             Some (set_life _UU03a3_ _UU03b3_ n f (Unloading (acc, w, None)))
           | _ -> None)
   | None -> None)

(** val lifecycle_labels : int -> 'a1 label list **)

let lifecycle_labels n =
  (LBegin n) :: ((LStep n) :: ((LDivert n) :: ((LLeave n) :: ((LUndo
    n) :: ((LRetireChild n) :: ((LUnloaded n) :: ((LRemove n) :: [])))))))

type ('name, 'v) rSt = 'name -> 'v option

type ('name, 'v) rOp =
| Register of 'name * 'v
| Lookup of 'name

(** val upd :
    ('a1 -> 'a1 -> bool) -> ('a1, 'a2) rSt -> 'a1 -> 'a2 option -> ('a1, 'a2)
    rSt **)

let upd name_eq_dec s x o y =
  if name_eq_dec y x then o else s y

(** val rrun :
    ('a1 -> 'a1 -> bool) -> ('a1, 'a2) rOp -> int -> ('a1, 'a2) rSt ->
    ((('a1, 'a2) rSt * (('a1, 'a2) rSt -> ('a1, 'a2) rSt)) * 'a2 option)
    option **)

let rrun name_eq_dec a _ s =
  match a with
  | Register (x, v) ->
    (match s x with
     | Some _ -> None
     | None ->
       Some (((upd name_eq_dec s x (Some v)), (fun s' ->
         upd name_eq_dec s' x None)), None))
  | Lookup x -> Some ((s, (fun s' -> s')), (s x))

(** val registry : ('a1 -> 'a1 -> bool) -> service **)

let registry name_eq_dec =
  Obj.magic rrun name_eq_dec

(** val _UU03a3_R : service **)

let _UU03a3_R =
  registry (=)

type dComp = (int, int) component

type dProg = (int, int) prog

type dState = (int, int) state

type dLabel = int label

(** val dinit : dState **)

let dinit =
  init _UU03a3_R

(** val dstep : (int -> dComp) -> dState -> dLabel -> dState option **)

let dstep prog0 _UU03b3_ _UU2113_ =
  step (=) _UU03a3_R prog0 _UU03b3_ _UU2113_

(** val denabled : (int -> dComp) -> dState -> dLabel list **)

let denabled prog0 _UU03b3_ =
  filter (fun _UU2113_ ->
    match dstep prog0 _UU03b3_ _UU2113_ with
    | Some _ -> true
    | None -> false) (flat_map lifecycle_labels (names _UU03a3_R _UU03b3_))

(** val dop : int -> int -> int -> dProg -> dProg **)

let dop k x v p =
  POp (k, (Obj.magic (Register (x, v))), (fun _ -> p))

(** val dprovide : int -> (int * int) list -> dProg -> dProg **)

let dprovide k entries p =
  PProvide (k,
    (fold_right (fun pat s ->
      let (x, v) = pat in Obj.magic upd (=) s x (Some v))
      (Obj.magic (fun _ -> None)) entries),
    p)

(** val dspawn : int -> dProg -> dProg **)

let dspawn c p =
  PSpawn (c, p)

(** val ddone : dProg **)

let ddone =
  PDone

(** val dfail : dProg **)

let dfail =
  PFail

(** val dcomp : int list -> int list -> dProg -> dComp **)

let dcomp deps0 provs0 body0 =
  { deps = deps0; provs = provs0; body = body0; reacts = [] }

(** val dop_name : dState -> int -> int option **)

let dop_name _UU03b3_ tok =
  match _UU03b3_.oplog tok with
  | Some a ->
    (match Obj.magic a with
     | Register (x, _) -> Some x
     | Lookup _ -> None)
  | None -> None

(** val dbinding :
    dState -> int -> int list -> (int * int option list) option **)

let dbinding _UU03b3_ k xs =
  match _UU03b3_.binds k with
  | Some b ->
    Some (b.owner,
      (map (fun x -> let b0 = Obj.magic b in Obj.magic b0.bst x) xs))
  | None -> None

(** val dinstr : dProg -> int * int list **)

let dinstr = function
| PDone -> (0, [])
| PFail -> ((Stdlib.Int.succ 0), [])
| POp (k, a, _) ->
  (match Obj.magic a with
   | Register (x, v) ->
     ((Stdlib.Int.succ (Stdlib.Int.succ 0)), (k :: (x :: (v :: []))))
   | Lookup _ -> ((Stdlib.Int.succ (Stdlib.Int.succ 0)), (k :: [])))
| PProvide (k, _, _) ->
  ((Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0))), (k :: []))
| PSpawn (c, _) ->
  ((Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))),
    (c :: []))
