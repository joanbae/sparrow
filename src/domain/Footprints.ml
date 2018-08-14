open Vocab

module BatSet = BatSet.Make(Footprint)

type elt = Footprint.t
type t = BatSet.t

let compare = BatSet.compare

let to_string : t -> string = fun x ->
  if BatSet.is_empty x then "bot" else
    let add_string_of_v v acc = link_by_sep "," (Footprint.to_string v) acc in
    "{" ^ BatSet.fold add_string_of_v x "" ^ "}"

let le : t -> t -> bool = fun x y ->
  if x == y then true else BatSet.subset x y

let eq : t -> t -> bool = fun x y ->
  if x == y then true else BatSet.equal x y

let bot = BatSet.empty
let empty = bot

let join : t -> t -> t = fun x y ->
  if le x y then y else
  if le y x then x else
    BatSet.union x y
let union = join
let union_small_big small big = BatSet.fold BatSet.add small big

let meet : t -> t -> t = fun x y ->
  if le x y then x else
  if le y x then y else
    BatSet.inter x y
let inter = meet

(* Since module A is finite,  widening is defined as union which is
   sufficient to guarantee analysis termination.  *)
let widen : t -> t -> t = fun x y ->
  if x == y then x else
    BatSet.union x y

let narrow : t -> t -> t = fun x y ->
  if x == y then x else
    BatSet.inter x y


let filter : (elt -> bool) -> t -> t = fun f s ->
  BatSet.filter f s

let fold : (elt -> 'a -> 'a) -> t -> 'a -> 'a = BatSet.fold
let fold2 : (elt -> elt -> 'a -> 'a) -> t -> t -> 'a -> 'a
  = fun f s1 s2 -> BatSet.fold (fun x -> BatSet.fold (f x) s2) s1

let map = BatSet.map

let iter : (elt -> unit) -> t -> unit = BatSet.iter

let singleton : elt -> t = fun e ->
  BatSet.singleton e

let subset : t -> t -> bool = BatSet.subset

let cardinal : t -> int = BatSet.cardinal

let mem : elt -> t -> bool = BatSet.mem

let add e s = BatSet.add e s
let diff = BatSet.diff

let choose = BatSet.choose

let remove = BatSet.remove

let elements = BatSet.elements
let is_empty = BatSet.is_empty

let for_all = BatSet.for_all
let exists = BatSet.exists
let of_list = BatSet.of_list

let rec list_pp fmt = function
  | [] -> ()
  | [e] -> Footprint.pp fmt e
  | hd :: tl ->
    Footprint.pp fmt hd;
    Format.fprintf fmt ",@;";
    list_pp fmt tl

let sort fp =
  let compare_footprints fp1 fp2 =
    int_of_string fp2.Footprint.order - int_of_string fp1.Footprint.order
  in
  List.sort compare_footprints fp

let pp fmt x =
  if is_empty x then Format.fprintf fmt "bot" else
    ( Format.fprintf fmt "{ @[";
      list_pp fmt (sort (elements x));
      Format.fprintf fmt "@] }" )

let of_here here src_location exp n_num value order = singleton (Footprint.of_here here src_location exp n_num value order)

let make file line src_location exp n_num value order = add { Footprint.file = file; line; src_location; exp; n_num; value; order} empty

