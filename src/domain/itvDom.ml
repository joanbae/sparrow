(***********************************************************************)
(*                                                                     *)
(* Copyright (c) 2007-present.                                         *)
(* Programming Research Laboratory (ROPAS), Seoul National University. *)
(* All rights reserved.                                                *)
(*                                                                     *)
(* This software is distributed under the term of the BSD license.     *)
(* See the LICENSE file for details.                                   *)
(*                                                                     *)
(***********************************************************************)
open BasicDom
open Vocab

module Val =
struct
  include ProdDom.Make6 (Itv) (PowLoc) (ArrayBlk) (StructBlk) (PowProc) (Footprints)
  let null = (Itv.bot, PowLoc.null, ArrayBlk.bot, StructBlk.bot, PowProc.bot, Footprints.bot)
  let is_itv (i,_,_,_,_,_) = not (Itv.is_bot i)
  let is_array (_,_,a,_,_,_) = not (ArrayBlk.is_empty a)
  let make (i,p,a,s,proc,f) = (i,p,a,s,proc,f)
  let itv_of_val : t -> Itv.t = fst
  let pow_loc_of_val : t -> PowLoc.t = snd
  let array_of_val : t -> ArrayBlk.t = trd
  let struct_of_val : t -> StructBlk.t = frth
  let pow_proc_of_val : t -> PowProc.t = fifth
  let footprints_of_val : t -> Footprints.t = sixth
  let allocsites_of_val : t -> Allocsite.t BatSet.t
  = fun v -> v |> array_of_val |> ArrayBlk.allocsites_of_array

  let of_itv : Itv.t -> t = fun x ->
    (x, PowLoc.bot, ArrayBlk.bot, StructBlk.bot, PowProc.bot, Footprints.bot)
  let of_pow_loc : PowLoc.t -> t = fun x ->
    (Itv.bot, x, ArrayBlk.bot, StructBlk.bot, PowProc.bot, Footprints.bot)
  let of_array : ArrayBlk.t -> t = fun x ->
    (Itv.bot, PowLoc.bot, x, StructBlk.bot, PowProc.bot, Footprints.bot)
  let of_struct : StructBlk.t -> t = fun x ->
    (Itv.bot, PowLoc.bot, ArrayBlk.bot, x, PowProc.bot, Footprints.bot) 
  let of_pow_proc : PowProc.t -> t = fun x ->
    (Itv.bot, PowLoc.bot, ArrayBlk.bot, StructBlk.bot, x, Footprints.bot)
  let of_footprints : Footprints.t -> t = fun x ->
    (Itv.bot, PowLoc.bot, ArrayBlk.bot, StructBlk.bot, PowProc.bot, x)

  let modify_itv : Itv.t -> t -> t = fun i x ->
    (i, pow_loc_of_val x, array_of_val x, struct_of_val x, pow_proc_of_val x, footprints_of_val x)

  let modify_arr : ArrayBlk.t -> t -> t = fun a x ->
    (itv_of_val x, pow_loc_of_val x, a, struct_of_val x, pow_proc_of_val x, footprints_of_val x)

  let modify_footprints : Lexing.position -> Cil.location -> t -> t = fun here loc x ->
    let f = Footprints.add (Footprint.of_here here loc) (footprints_of_val x) in
    (itv_of_val x, pow_loc_of_val x, array_of_val x, struct_of_val x, pow_proc_of_val x, f)
    
  let external_value : Allocsite.t -> t = fun allocsite ->
    (Itv.top, PowLoc.bot, ArrayBlk.extern allocsite, StructBlk.extern (), PowProc.bot, Footprints.bot)

  let itv_top : t = (Itv.top, PowLoc.bot, ArrayBlk.bot, StructBlk.bot, PowProc.bot, Footprints.bot)

  let cast : Cil.typ -> Cil.typ -> t -> t
  = fun from_typ to_typ v ->
    let (from_typ, to_typ) = BatTuple.Tuple2.mapn Cil.unrollTypeDeep (from_typ, to_typ) in
    if v = (of_itv Itv.zero) && (Cil.isPointerType to_typ) then (* char* x = (char* ) 0 *)
      null
    else if Cil.isIntegralType to_typ then
      v |> itv_of_val |> Itv.cast from_typ to_typ |> of_itv
    else
      v |> array_of_val |> ArrayBlk.cast_array to_typ |> flip modify_arr v

  let to_string x =
   "("^(Itv.to_string (fst x))^", "^(PowLoc.to_string (snd x))^", "
    ^(ArrayBlk.to_string (trd x))^", "
    ^(StructBlk.to_string (frth x))^", "
    ^(PowProc.to_string (fifth x))^", "
    ^(Footprints.to_string (sixth x))^")"
end

module Mem =
struct
  include InstrumentedMem.Make(MapDom.MakeCPO (Loc) (Val))

  let add k v m =
    match Loc.typ k with
    | Some t when Cil.isArithmeticType t -> add k (Val.itv_of_val v |> Val.of_itv) m
    | _ -> add k v m

  let weak_add k v m =
    match Loc.typ k with
    | Some t when Cil.isArithmeticType t -> weak_add k (Val.itv_of_val v |> Val.of_itv) m
    | _ -> weak_add k v m

  let lookup : PowLoc.t -> t -> Val.t = fun locs mem ->
    if eq mem bot then Val.bot
    else
      let find_join loc acc = Val.join acc (find loc mem) in
      PowLoc.fold find_join locs Val.bot

  let strong_update : PowLoc.t -> Val.t -> t -> t
  = fun locs v mem ->
    PowLoc.fold (fun x -> add x v) locs mem

  let weak_update : PowLoc.t -> Val.t -> t -> t
  = fun locs v mem ->
    PowLoc.fold (fun x -> weak_add x v) locs mem
end

module Table = MapDom.MakeCPO (Node) (Mem)
