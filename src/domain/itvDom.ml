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
module FP = Footprints

module Val =
struct
  include ProdDom.Make6 (Itv) (PowLoc) (ArrayBlk) (StructBlk) (PowProc) (Footprints)
  let fp_count = ref 0
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

  (* value without fp *)
  let without_fp : t -> t = fun v ->
    (itv_of_val v, pow_loc_of_val v, array_of_val v, struct_of_val v, pow_proc_of_val v, Footprints.empty) 

  let get_fp_count () : string =
    let str = string_of_int !fp_count in
    fp_count := !fp_count + 1;
    str

  let modify_footprints : Lexing.position -> Cil.location -> string -> string -> t -> t
    = fun here loc e n_num x ->
      let s_only_v = without_fp x |> to_string in
      let f = Footprints.add (Footprint.of_here here loc e n_num s_only_v (get_fp_count ())) (footprints_of_val x) in
      (itv_of_val x, pow_loc_of_val x, array_of_val x, struct_of_val x, pow_proc_of_val x, f)

  (*eval_lv에서 나오는 Footprint를 처리하기 위해서 쓴다.*)
  let modify_footprints' : Lexing.position -> Footprints.t -> Cil.location -> string -> string -> t -> t
    = fun here fp loc e n_num x ->
      let s_only_v = without_fp x |> to_string in
      let f = Footprints.add (Footprint.of_here here loc e n_num s_only_v (get_fp_count ())) (footprints_of_val x) in
      let f' = Footprints.join fp f in
      (itv_of_val x, pow_loc_of_val x, array_of_val x, struct_of_val x, pow_proc_of_val x, f')

  (* For joining multiple footprints *)
  let modify_footprints'' : Lexing.position -> Footprints.t list -> Cil.location -> string -> string -> t -> t
    = fun here fps loc e n_num x ->
      let rec fp_join fps res =
        match fps with
          [] -> res
        | hd::tl -> fp_join tl (Footprints.join hd res)
      in
      let fps = fp_join fps Footprints.empty in
      modify_footprints' here fps loc e n_num x

  let modify_footprints''' : Lexing.position list -> Cil.location -> string -> string -> t -> t
    = fun hlst loc e n_num x -> List.fold_left (fun v here -> modify_footprints here loc e n_num v) x hlst

  let external_value : Allocsite.t -> t = fun allocsite ->
    let array = ArrayBlk.extern allocsite in
    (Itv.top, PowLoc.bot, array, StructBlk.bot, PowProc.bot, Footprints.bot)
  (* (Itv.top, PowLoc.bot, ArrayBlk.extern allocsite, StructBlk.extern (), PowProc.bot, Footprints.bot) *)

  let itv_top : t = (Itv.top, PowLoc.bot, ArrayBlk.bot, StructBlk.bot, PowProc.bot, Footprints.bot)

  let cast : Cil.typ -> Cil.typ -> t -> (Cil.location * Cil.exp) -> string ->  t
  = fun from_typ to_typ v (loc, exp) n_num ->
    let fp = footprints_of_val v in
    let s_exp = CilHelper.s_exp exp in
    let (from_typ, to_typ) = BatTuple.Tuple2.mapn Cil.unrollTypeDeep (from_typ, to_typ) in
    if v = (of_itv Itv.zero) && (Cil.isPointerType to_typ) then (* char* x = (char* ) 0 *)
      let res, here = null, [%here] in
      modify_footprints' here fp loc s_exp n_num res
    else if Cil.isIntegralType to_typ then
    let itv, here = Itv.cast from_typ to_typ (itv_of_val v), [%here] in
    modify_footprints' here fp loc s_exp n_num (of_itv itv)
    else
      let arr, here = ArrayBlk.cast_array to_typ (array_of_val v), [%here] in
      modify_footprints' here fp loc s_exp n_num (flip modify_arr v arr)

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
    | Some t when Cil.isArithmeticType t ->
      let v_fp = Val.footprints_of_val v |> Val.of_footprints in
      let v = Val.modify_itv (Val.itv_of_val v) v_fp in
      add k v m
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
  = fun locs v mem -> PowLoc.fold (fun x -> add x v) locs mem

  let weak_update : PowLoc.t -> Val.t -> t -> t
  = fun locs v mem ->
    PowLoc.fold (fun x -> weak_add x v) locs mem
end

module Table = MapDom.MakeCPO (Node) (Mem)
