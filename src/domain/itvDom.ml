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
module ExpArg = Footprint.ExpArg
module FP = Footprint
module FPS = Footprints

module Val =
struct
  include ProdDom.Make6 (Itv) (PowLoc) (ArrayBlk) (StructBlk) (PowProc) (Footprints)
  let fp_count = ref 0
  let debug_mode = ref false
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

  let external_value : Allocsite.t -> t = fun allocsite ->
    let array = ArrayBlk.extern allocsite in
    (Itv.top, PowLoc.bot, array, StructBlk.bot, PowProc.bot, Footprints.bot)
  (* (Itv.top, PowLoc.bot, ArrayBlk.extern allocsite, StructBlk.extern (), PowProc.bot, Footprints.bot) *)

  let itv_top : t = (Itv.top, PowLoc.bot, ArrayBlk.bot, StructBlk.bot, PowProc.bot, Footprints.bot)

  
  let only_itv_exists v =
    if v = bot then false
    else
      let itv = Itv.is_bot (itv_of_val v) in
      let ploc = PowLoc.is_empty (pow_loc_of_val v) in
      let arr = ArrayBlk.is_empty (array_of_val v) in
      let s = StructBlk.is_empty (struct_of_val v) in
      if ploc && arr && s && (not itv) then true
      else false
   let only_ploc_exists v =
    if v = bot then false
    else
      let itv = Itv.is_bot (itv_of_val v) in
      let ploc = PowLoc.is_empty (pow_loc_of_val v) in
      let arr = ArrayBlk.is_empty (array_of_val v) in
      let s = StructBlk.is_empty (struct_of_val v) in
      if not ploc && arr && s && itv then true
      else false
   let only_array_exists v =
    if v = bot then false
    else
      let itv = Itv.is_bot (itv_of_val v) in
      let ploc = PowLoc.is_empty (pow_loc_of_val v) in
      let arr = ArrayBlk.is_empty (array_of_val v) in
      let s = StructBlk.is_empty (struct_of_val v) in
      if ploc && not arr && s && itv then true
      else false

  let priority ?(isPointer=false) ?(widen=false) v  =
    if v = bot then 3
    else if only_itv_exists v then Itv.priority ~widen (itv_of_val v)
    else if only_ploc_exists v then PowLoc.priority (pow_loc_of_val v)
    else if only_array_exists v then ArrayBlk.priority ~isPointer (array_of_val v)
    else
      (* let str int = string_of_int int in
       * print_endline(str(Itv.priority (itv_of_val v))^","^ str(PowLoc.priority (pow_loc_of_val v))^","^str (ArrayBlk.priority ~isPointer (array_of_val v))); *)
      Itv.priority (itv_of_val v) + PowLoc.priority (pow_loc_of_val v) + ArrayBlk.priority ~isPointer (array_of_val v)

  (* value without fp *)
  let without_fp : t -> t = fun v ->
    (itv_of_val v, pow_loc_of_val v, array_of_val v, struct_of_val v, pow_proc_of_val v, Footprints.empty) 

  let modify_fp_only : t -> Footprints.t -> t = fun v fp ->
    (itv_of_val v, pow_loc_of_val v, array_of_val v, struct_of_val v, pow_proc_of_val v, fp)

  let increment_fp_count () =
    let count = !fp_count in
    fp_count := !fp_count + 1;
    count

  let get_fp_count () : int = !fp_count -1 

  let fp_value_of_val x =
    Footprint.Value.make
      (itv_of_val x)
      (pow_loc_of_val x)
      (array_of_val x)
      (struct_of_val x)
      (pow_proc_of_val x)

  let modify_footprints : Lexing.position -> Cil.location -> ExpArg.t -> n_info:string -> ?isPointer:bool -> ?widen:bool -> t -> t
    = fun here loc e ~n_info ?(isPointer = false) ?(widen = false) x ->
      if !debug_mode then x else
        let pri = priority ~isPointer ~widen x in
        let fp_value = fp_value_of_val x in
        let f = Footprints.add (Footprint.of_here here loc e n_info fp_value (increment_fp_count ()) pri) (footprints_of_val x) in
        (itv_of_val x, pow_loc_of_val x, array_of_val x, struct_of_val x, pow_proc_of_val x, f)

 let modify_footprints' : Lexing.position -> Footprints.t -> Cil.location -> ExpArg.t -> n_info:string -> ?isPointer:bool -> ?widen:bool -> t -> t
   = fun here fp loc e ~n_info ?(isPointer = false) ?(widen = false) x ->
     if !debug_mode then x else
       let pri = priority ~isPointer ~widen x in
       let fp_value = fp_value_of_val x in
       let f = Footprints.add (Footprint.of_here here loc e n_info fp_value (increment_fp_count ()) pri) (footprints_of_val x) in
       (itv_of_val x, pow_loc_of_val x, array_of_val x, struct_of_val x, pow_proc_of_val x, Footprints.join fp f)

  (* For joining multiple footprints *)
  let modify_footprints'' : Lexing.position -> Footprints.t list -> ?isPointer:bool-> Cil.location -> ExpArg.t -> n_info:string -> t -> t
    = fun here fps ?(isPointer = false) loc e ~n_info x ->
      if !debug_mode then x else
        let rec fp_join fps res =
          match fps with
            [] -> res
          | hd::tl -> fp_join tl (Footprints.join hd res)
        in
        let fps = fp_join fps Footprints.empty in
        modify_footprints' here fps loc e ~n_info ~isPointer x

  (*eval_lv에서 나오는 Footprint를 처리하기 위해서 쓴다.*)
  let modify_footprints'''' : Lexing.position -> FP.t -> FPS.t option -> Cil.location -> ExpArg.t -> n_info:string -> ?isPointer:bool -> ?widen:bool -> BasicDom.PowLoc.t -> t -> t
    = fun here lv_fp fp_opt loc e ~n_info ?(isPointer = false) ?(widen = false) lv x ->
      if !debug_mode then x else
        let priority = priority ~isPointer ~widen x in
        let fp_value = fp_value_of_val x in
        let f = Footprint.of_here ~addrOf:(Some lv_fp) here loc e n_info fp_value (increment_fp_count ()) priority in
        (*  when cfc for the statement below
         *      char *value = getenv("USER");
         *      is genearted in this way
         *      1. tmp:= call(@getenv, (__cil_tmp5)
         *      2. set(value,tmp)
         * give higher priority to 2. by one *)
        let fp_switched =
          let l = lv |> BasicDom.PowLoc.filter (fun x -> BasicDom.Loc.is_local_tmp_of x) |> BasicDom.PowLoc.elements in
          if l != [] && List.length l = 1 then
            FPS.add f (FPS.increase_priority (footprints_of_val x) 1)              (* increse old_fp's priority by one  *)
          else
            FPS.add f (footprints_of_val x) in
        let new_fp = match fp_opt with
          | None -> fp_switched
          | Some fps -> Footprints.join fps fp_switched in
        (itv_of_val x, pow_loc_of_val x, array_of_val x, struct_of_val x, pow_proc_of_val x, new_fp)

  let increase_priority v p =
    let fps = Footprints.increase_priority (footprints_of_val v) p in
    (itv_of_val v, pow_loc_of_val v, array_of_val v, struct_of_val v, pow_proc_of_val v, fps)
  
  let cast : Cil.typ -> Cil.typ -> t -> (Cil.location * Cil.exp) -> n_info : string -> t
    = fun from_typ to_typ v (loc, exp) ~n_info ->
      if !debug_mode then v else 
        let fp = footprints_of_val v in
        let (from_typ, to_typ) = BatTuple.Tuple2.mapn Cil.unrollTypeDeep (from_typ, to_typ) in
        if without_fp v = (of_itv Itv.zero) && (Cil.isPointerType to_typ) then (* char* x = (char* ) 0 *)
          null |> modify_footprints' [%here] fp loc (Exp exp) ~n_info
        else if Cil.isIntegralType to_typ then
          let itv, here = Itv.cast from_typ to_typ (itv_of_val v), [%here] in
          let priority = Itv.priority itv in
          match FPS.latest_elt fp with
          | None ->
            modify_footprints' here fp loc (Exp exp) ~n_info (of_itv itv)
          | Some f ->
            (* 3. if arr's priority > last fp's priority then give the same amount of priority to the old one *)
            FPS.increase_priority fp priority |> fun fp ->
            modify_footprints' here fp loc (Exp exp) ~n_info (of_itv itv |> without_fp)
            (* modify_footprints' here fp loc (Exp exp) ~n_info (of_itv itv) *)
        else
          let arr, here = ArrayBlk.cast_array to_typ (array_of_val v), [%here] in
          (* 1. get priority of arr *)
          let priority = ArrayBlk.priority arr in
          (* 2. compare with last fp's priority *)
          (* 2-1 if from_type :char * to to_type:char const * then don't increase the priority *)
          if from_typ = Cil.charPtrType && to_typ = Cil.charConstPtrType then
            modify_footprints' here fp loc (Exp exp) ~n_info (flip modify_arr v arr |> without_fp)
            (* 2-2 from_type = void * & to_type = char * *)
          else if from_typ = Cil.voidPtrType && to_typ = Cil.charPtrType then
            modify_footprints' here fp loc (Exp exp) ~n_info (flip modify_arr v arr |> without_fp)
          else
            match FPS.max_priority_elt fp with
            | None ->
              modify_footprints' here fp loc (Exp exp) ~n_info (flip modify_arr v arr)
            | Some f ->
              (* 3. if arr's priority > last fp's priority then give the same amount of priority to the old one *)
              FPS.increase_priority' fp priority |> fun fp ->
              modify_footprints' here fp loc (Exp exp) ~n_info (flip modify_arr v arr |> without_fp)
              (* modify_footprints' here fp loc (Exp exp) ~n_info (flip modify_arr v arr) *)


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
      add k (Val.modify_itv (Val.itv_of_val v) v_fp) m
    | _ -> add k v m
             
  let weak_add k v m =
    match Loc.typ k with
    | Some t when Cil.isArithmeticType t ->
      let v_fp = Val.footprints_of_val v |> Val.of_footprints in
      weak_add k (Val.modify_itv (Val.itv_of_val v) v_fp) m
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
