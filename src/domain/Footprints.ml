open Vocab

module M = BatSet.Make(Footprint)

type elt = Footprint.t
type t = M.t

exception Error
let compare = M.compare

let to_string : t -> string = fun x ->
  if M.is_empty x then "bot" else
    let add_string_of_v v acc = link_by_sep "," (Footprint.to_string v) acc in
    M.fold add_string_of_v x ""


let le : t -> t -> bool = fun x y ->
  if x == y then true else M.subset x y

let eq : t -> t -> bool = fun x y ->
  if x == y then true else M.equal x y

let bot = M.empty
let empty = bot

let join : t -> t -> t = fun x y ->
  if le x y then y else
  if le y x then x else
    M.union x y

let meet : t -> t -> t = fun x y ->
  if le x y then x else
  if le y x then y else
    M.inter x y


(* Since module A is finite,  widening is defined as union which is
   sufficient to guarantee analysis termination.  *)
let widen : t -> t -> t = fun x y ->
  M.union x y

let narrow : t -> t -> t = fun x y ->
  M.inter x y

let filter : (elt -> bool) -> t -> t = fun f s ->
  M.filter f s

let fold : (elt -> 'a -> 'a) -> t -> 'a -> 'a = M.fold
let fold2 : (elt -> elt -> 'a -> 'a) -> t -> t -> 'a -> 'a 
  = fun f s1 s2 -> M.fold (fun x -> M.fold (f x) s2) s1

let map = M.map

let iter : (elt -> unit) -> t -> unit = M.iter

let singleton : elt -> t = fun e ->
  M.singleton e

let subset : M.t -> t -> bool = M.subset

let cardinal : t -> int = M.cardinal

let mem : elt -> t -> bool = M.mem

let add e s = M.add e s
let diff = M.diff

let choose = M.choose

let remove = M.remove

let elements = M.elements
let is_empty = M.is_empty

let for_all = M.for_all
let exists = M.exists
let of_list = M.of_list

let rec list_pp fmt = function
  | [] -> ()
  | [e] -> Footprint.pp fmt e
  | hd :: tl ->
    Footprint.pp fmt hd;
    Format.fprintf fmt ",@;";
    list_pp fmt tl

let sort fp =
 let compare_by_order fp1 fp2 = fp2.Footprint.order - fp1.Footprint.order in
  let compare_by_priority fp1 fp2 =
    let rec calc_priority' fp = (** this is for calculating priority of parent fps **)
      match fp.Footprint.parent with
      | None -> fp.priority
      | Some parent -> max fp.priority (calc_priority' parent) in
    let calc_priority fp =
      match fp.Footprint.addrOf with
      | None -> fp.priority
      | Some addrOf ->
        (match addrOf.Footprint.parent with
         | None -> max fp.priority addrOf.priority
         | Some parent -> max fp.priority (max addrOf.priority (calc_priority' parent))) in
    calc_priority fp2 - calc_priority fp1 in
 List.sort compare_by_order fp |> List.sort compare_by_priority


let pp fmt x =
  if is_empty x then Format.fprintf fmt "\"bot\"" else
    ( Format.fprintf fmt "{ @[";
      list_pp fmt (sort (elements x));
      Format.fprintf fmt "@] }" )

let of_here ?(parent=None) ?(addrOf=None) here src_location exp n_num value order priority =
  singleton (Footprint.of_here here src_location exp n_num value order ~parent ~addrOf priority)

let make ?(parent=None) ?(addrOf=None) file line src_location exp n_info value order priority =
  add {Footprint.file; line; src_location; exp; n_info; value; order; parent; addrOf; priority} empty

(* increase priority of the latest order *)
let increase_priority : t -> int -> t = fun x priority ->
  let footprint_max x y = if x.Footprint.order > y.Footprint.order then x else y in
  let find_max_fp (fps:t) =
    let get_max fp acc =
      let max_fp =
        match acc with
        | None -> fp
        | Some fp' -> footprint_max fp fp'
      in
      Some max_fp
    in
    M.fold get_max fps None
  in
  match find_max_fp x with
  | None -> x
  | Some fp -> add {fp with priority = fp.priority + priority} (remove fp x)

(* increase priority of the highest rank *)
let increase_priority' : t -> int -> t = fun x priority ->
  let footprint_max x y = if x.Footprint.priority > y.Footprint.priority then x else y in
  let find_max_fp (fps:t) =
    let get_max fp acc =
      let max_fp =
        match acc with
        | None -> fp
        | Some fp' -> footprint_max fp fp'
      in
      Some max_fp
    in
    M.fold get_max fps None
  in
  match find_max_fp x with
  | None -> x
  | Some fp ->
    add {fp with priority = fp.priority + priority} (remove fp x)

let latest_elt : t -> elt option = fun x ->
  let footprint_max x y = if x.Footprint.order > y.Footprint.order then x else y in
  let find_max_fp (fps:t) =
    let get_max fp acc =
      let max_fp =
        match acc with
        | None -> fp
        | Some fp' -> footprint_max fp fp'
      in
      Some max_fp
    in
    M.fold get_max fps None
  in
  find_max_fp x

let max_priority_elt : t -> elt option = fun x ->
  let footprint_max x y = if x.Footprint.priority > y.Footprint.priority then x else y in
  let find_max_fp (fps:t) =
    let get_max fp acc =
      let max_fp =
        match acc with
        | None -> fp
        | Some fp' -> footprint_max fp fp'
      in
      Some max_fp
    in
    M.fold get_max fps None
  in
  find_max_fp x
