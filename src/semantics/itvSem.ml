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
(** Semantics of interval analysis *)
open Vocab
open Cil
open IntraCfg
open AbsSem
open BasicDom
open ItvDom
open Global
open ArrayBlk
open BatTuple

module FPS = Footprints
module FP = Footprint
module ExpArg = Footprint.ExpArg
module Dom = ItvDom.Mem
module Access = Dom.Access
module Spec = Spec.Make(Dom)

let fileName = "itvSem.ml"

(* ********************** *
 * Abstract memory access *
 * ********************** *)
let can_strong_update : update_mode -> Spec.t -> Global.t -> PowLoc.t -> bool
= fun mode spec global lvs ->
  if spec.Spec.unsound_update then true
  else
    match mode,lvs with
    | Weak, _ -> false
    | Strong, lvs' ->
      if PowLoc.cardinal lvs' = 1 then
        let lv = PowLoc.choose lvs' in
        Loc.is_gvar lv ||
        (Loc.is_lvar lv && not (Global.is_rec (Loc.get_proc lv) global))
      else false

let lookup : PowLoc.t -> Mem.t -> Val.t
= fun locs mem ->
  Mem.lookup locs mem

let update : update_mode -> Spec.t -> Global.t -> PowLoc.t -> Val.t -> Mem.t -> Mem.t
  = fun mode spec global locs v mem ->
    let check_v = (** give priority when value gets updated **)
      if Val.without_fp v = Val.bot then v
      else Val.modify_priority v 5  in
    if can_strong_update mode spec global locs then Mem.strong_update locs check_v mem
    else Mem.weak_update locs check_v mem

(* ********************************** *
 * Semantic functions for expressions *
 * ********************************** *)

let eval_const : Cil.constant -> Cil.location -> n_info:string -> Val.t = fun cst loc ~n_info ->
  let exp = ExpArg.Exp (Const cst) in
  match cst with
  | Cil.CInt64 (i64, _, _) ->
    let itv = try Itv.of_int (Cil.i64_to_int i64) with _ -> Itv.top in
    Val.modify_footprints [%here] loc exp n_info (Val.of_itv itv) 
  | Cil.CStr s -> Val.modify_footprints [%here] loc exp n_info (Val.of_itv Itv.top)
  | Cil.CWStr s -> Val.modify_footprints [%here] loc exp n_info (Val.of_itv Itv.top)
  | Cil.CChr c -> Val.modify_footprints [%here] loc exp n_info (Val.of_itv (Itv.of_int (int_of_char c)))
  (* Float numbers are modified to itvs.  If you want to make a
     precise and sound analysis for float numbers, you have to
     develop a domain for them. *)
  | Cil.CReal (f, _, _) ->
   Val.modify_footprints [%here] loc exp n_info (Val.of_itv (Itv.of_ints (int_of_float (floor f)) (int_of_float (ceil f))))
  (* Enum is not evaluated correctly in our analysis. *)
  | Cil.CEnum _ -> Val.modify_footprints [%here] loc exp n_info (Val.of_itv Itv.top)

let eval_uop : Spec.t -> Cil.unop -> Val.t -> Cil.location -> e:ExpArg.t -> n_info:string -> Val.t
= fun spec u v loc ~e ~n_info ->
  if Val.eq v Val.bot then Val.bot else
    let fp = Val.footprints_of_val v in 
    let itv = Val.itv_of_val v in
    let itv', here =
      match u with
      | Cil.Neg -> Itv.minus (Itv.of_int 0) itv, [%here]
      | Cil.LNot -> Itv.l_not itv, [%here]
      | Cil.BNot -> if spec.Spec.unsound_bitwise then (Itv.bot, [%here]) else (Itv.unknown_unary itv, [%here])
    in
    Val.modify_footprints here loc e n_info (Val.join (Val.of_footprints fp) (Val.of_itv itv'))

let eval_bop : Spec.t -> Cil.binop -> Val.t -> Val.t -> Cil.location -> e:ExpArg.t -> n_info:string -> Val.t
  = fun spec b v1 v2 loc ~e ~n_info ->
    let fp = Val.of_footprints (FPS.join (Val.footprints_of_val v1) (Val.footprints_of_val v2)) in
    match b with
    | Cil.PlusA ->
      let v = Val.of_itv (Itv.plus (Val.itv_of_val v1) (Val.itv_of_val v2)) in
      Val.modify_footprints [%here] loc e n_info (Val.join v fp)
    | Cil.PlusPI
    | Cil.IndexPI ->
      let ablk = Val.array_of_val v1 in
      let offset = Val.itv_of_val v2 in
      let ablk = ArrayBlk.plus_offset ablk offset in
      let v = Val.join (Val.of_pow_loc (Val.pow_loc_of_val v1)) (Val.of_array ablk) in
      Val.modify_footprints [%here] loc e n_info (Val.join v fp)
  | Cil.MinusA ->
    let v = Val.of_itv (Itv.minus (Val.itv_of_val v1) (Val.itv_of_val v2)) in
    Val.modify_footprints [%here] loc e n_info (Val.join v fp)
  | Cil.MinusPI ->
    let ablk = Val.array_of_val v1 in
    let offset = Val.itv_of_val v2 in
    let ablk = ArrayBlk.minus_offset ablk offset in
    let v = Val.join (Val.of_pow_loc (Val.pow_loc_of_val v1)) (Val.of_array ablk) in
    Val.modify_footprints [%here] loc e n_info (Val.join v fp)
  | Cil.MinusPP ->
    let offset1 = Val.array_of_val v1 |> ArrayBlk.offsetof in
    let offset2 = Val.array_of_val v2 |> ArrayBlk.offsetof in
    let v, here = Itv.minus offset1 offset2 |> Val.of_itv, [%here] in
    Val.modify_footprints here loc e n_info (Val.join v fp)
  | Cil.Mult ->
    let v = Val.of_itv (Itv.times (Val.itv_of_val v1) (Val.itv_of_val v2)) in
    Val.modify_footprints [%here] loc e n_info (Val.join v fp)
  | Cil.Div ->
    let v = Val.of_itv (Itv.divide (Val.itv_of_val v1) (Val.itv_of_val v2)) in
    Val.modify_footprints [%here] loc e n_info (Val.join v fp)
  | Cil.Lt ->
    let v = Val.of_itv (Itv.lt_itv (Val.itv_of_val v1) (Val.itv_of_val v2)) in
    Val.modify_footprints [%here] loc e n_info (Val.join v fp)   
  | Cil.Gt ->
    let v = Val.of_itv (Itv.gt_itv (Val.itv_of_val v1) (Val.itv_of_val v2)) in
    Val.modify_footprints [%here] loc e n_info (Val.join v fp) 
  | Cil.Le ->
    let v = Val.of_itv (Itv.le_itv (Val.itv_of_val v1) (Val.itv_of_val v2)) in
    Val.modify_footprints [%here] loc e n_info (Val.join v fp) 
  | Cil.Ge ->
    let v = Val.of_itv (Itv.ge_itv (Val.itv_of_val v1) (Val.itv_of_val v2)) in
    Val.modify_footprints [%here] loc e n_info (Val.join v fp) 
  | Cil.Eq ->
    let v = Val.of_itv (Itv.eq_itv (Val.itv_of_val v1) (Val.itv_of_val v2)) in
    Val.modify_footprints [%here] loc e n_info (Val.join v fp) 
  | Cil.Ne ->
    let v = Val.of_itv (Itv.ne_itv (Val.itv_of_val v1) (Val.itv_of_val v2)) in
    Val.modify_footprints [%here] loc e n_info (Val.join v fp) 
  | Cil.LAnd ->
    let v = Val.of_itv (Itv.l_and (Val.itv_of_val v1) (Val.itv_of_val v2)) in
    Val.modify_footprints [%here] loc e n_info (Val.join v fp) 
  | Cil.LOr ->
    let v  = Val.of_itv (Itv.l_or (Val.itv_of_val v1) (Val.itv_of_val v2)) in
    Val.modify_footprints [%here] loc e n_info (Val.join v fp) 
  | Cil.Shiftlt ->
    if spec.Spec.unsound_bitwise then Val.modify_footprints [%here] loc e n_info v1
    else
      let v = Val.of_itv (Itv.l_shift (Val.itv_of_val v1) (Val.itv_of_val v2)) in
      Val.modify_footprints [%here] loc e n_info (Val.join v fp)
  | Cil.Shiftrt | Cil.Mod | Cil.BAnd | Cil.BXor | Cil.BOr ->
    if spec.Spec.unsound_bitwise then Val.modify_footprints [%here] loc e n_info v1
    else
      let v = Val.of_itv (Itv.unknown_binary (Val.itv_of_val v1) (Val.itv_of_val v2)) in
      Val.modify_footprints [%here] loc e n_info (Val.join v fp)

let rec resolve_offset : Spec.t -> Proc.t -> Val.t -> Cil.offset ->
  Mem.t -> FP.t * Cil.location -> exp:ExpArg.t -> n_info:string -> PowLoc.t * FP.t
= fun spec pid v os mem (fp, loc) ~exp ~n_info ->
  let fp_count () = Val.increment_fp_count() in
  let fp_value ploc = Val.fp_value_of_val (Val.of_pow_loc ploc) in
  let fp_priority ploc = Val.priority (Val.of_pow_loc ploc) in

  match os with
  | Cil.NoOffset ->
    let powloc, here =  PowLoc.join (Val.pow_loc_of_val v) (Val.array_of_val v |> ArrayBlk.pow_loc_of_array), [%here] in
    (powloc, FP.of_here ~parent:(Some fp) here loc (Offset (NoOffset, exp)) n_info (fp_value powloc) (fp_count ()) (fp_priority powloc))
  | Cil.Field (f, os') ->
    let (ploc, arr, str) = (Val.pow_loc_of_val v, Val.array_of_val v, Val.struct_of_val v) in
    let powloc, here =
      let v1 = StructBlk.append_field (Val.struct_of_val (lookup ploc mem)) f in (* Case1: S s; p = &s; p->f *)
      let v2 = ArrayBlk.append_field arr f in (* Case2:  p = (struct S* )malloc(sizeof(struct S)); p->f *)
      let v3 = StructBlk.append_field str f in (* Case3:  S s; s.f *)
      (PowLoc.join (PowLoc.join v1 v2) v3), [%here]
    in
    let field_exp = ExpArg.Offset (FieldOffset f, exp) in 
    let fp =FP.of_here ~parent:(Some fp) here loc field_exp n_info (fp_value powloc) (fp_count ()) (fp_priority powloc) in
    resolve_offset spec pid (Val.of_pow_loc powloc) os' mem (fp, loc) exp n_info
  | Cil.Index (e, os') ->
    let ploc = Val.pow_loc_of_val v in
    let arr = lookup ploc mem |> Val.array_of_val in
    let _ : ItvDom.Val.t = eval ~spec pid e mem loc n_info in (* NOTE: to sync with access function *)
    let ploc', here = ArrayBlk.pow_loc_of_array arr, [%here] in
    let index_exp = ExpArg.Offset (IndexOffset e, exp) in 
    let fp = FP.of_here ~parent:(Some fp) here loc index_exp n_info (fp_value ploc') (fp_count()) (fp_priority ploc') in
    resolve_offset spec pid (Val.of_pow_loc ploc') os' mem (fp, loc) exp n_info

and eval_lv_with_footprint ?(spec=Spec.empty) : Proc.t -> Cil.lval -> Mem.t -> Cil.location -> n_info:string -> PowLoc.t * Footprint.t * Footprints.t option
  = fun pid lv mem loc ~n_info ->
    let v, here, fpo =
      match fst lv with
      | Cil.Var vi ->
        let l, here =  var_of_varinfo vi pid in
        (l |> PowLoc.singleton |> Val.of_pow_loc, here, None)
      | Cil.Mem e ->
        let v, here = eval ~spec pid e mem loc n_info, [%here] in 
        (v, here, Some (Val.footprints_of_val v))
    in
    let base_pri = if Val.eq v Val.bot then 4 else 0 in
    let base_fp = FP.of_here here loc (BaseLoc (fst lv)) n_info (Val.fp_value_of_val v) (Val.increment_fp_count ()) base_pri in
    let powloc, fp' = resolve_offset spec pid v (snd lv) mem (base_fp, loc) (BaseLoc (fst lv)) n_info in
    (PowLoc.remove Loc.null powloc, calculate_priority_of_eval_lv fp', fpo)

and calculate_priority_of_eval_lv = fun fp ->
  let increase_priority fp = {fp with Footprint.priority = fp.Footprint.priority + 4} in
  let increase_priority_when_more_than_two fp = {fp with Footprint.priority = fp.Footprint.priority + 3} in
  let rec parent_passing_non_bot fp = (* case1: when parents pass non_bot value to the children *)
    let parent = fp.Footprint.parent in
    if Footprint.Value.check_bot fp.Footprint.value then
      match parent with
      | None -> fp
      | Some parent -> 
        let parent =
          if not (Footprint.Value.check_bot parent.value) then
            increase_priority parent
          else
            parent_passing_non_bot parent in
        {fp with parent = Some parent}
    else
      fp in
  let rec parent_passing_bot fp = (* case2: when parents pass bot value to the children *)
    if Footprint.Value.check_bot fp.Footprint.value then
      let parent = fp.Footprint.parent in
      match parent with
      | None -> fp
      | Some parent ->
        let child, parent =
          if Footprint.Value.check_bot parent.value then
            (fp, parent_passing_bot parent)
          else
            (increase_priority fp, parent)
        in
        { child with parent = Some parent}
    else
      fp in
  let rec parent_passing_more_than_two fp =
    let parent = fp.Footprint.parent in
    match parent with
    | None -> fp
    | Some parent ->
      let parent =
        if Footprint.Value.check_powloc_greater_than_equal_to_two parent.value then
          increase_priority_when_more_than_two parent
        else
          parent_passing_more_than_two parent in
      {fp with parent = Some parent}
  in
  fp |> parent_passing_non_bot |> parent_passing_bot |> parent_passing_more_than_two

and var_of_varinfo vi pid  =
  if vi.Cil.vglob then Loc.of_gvar vi.Cil.vname vi.Cil.vtype, [%here]
  else Loc.of_lvar pid vi.Cil.vname vi.Cil.vtype, [%here]

and eval ?(spec=Spec.empty) : Proc.t -> Cil.exp -> Mem.t -> Cil.location -> string -> Val.t
  = fun pid e mem loc n_info ->
    let s_exp = ExpArg.Exp e in
    match e with
    | Cil.Const c -> Val.modify_footprints [%here] loc s_exp n_info (eval_const c loc n_info) 
    | Cil.Lval l -> 
      let lv, lv_fp, fp_opt = eval_lv_with_footprint ~spec pid l mem loc ~n_info in
      Val.modify_footprints'''' [%here] lv_fp fp_opt loc s_exp n_info (lookup lv mem)
    | Cil.SizeOf t ->
      let sizeOf, here =
        Val.of_itv (try CilHelper.byteSizeOf t |> Itv.of_int with _ -> Itv.pos), [%here] in
      Val.modify_footprints here loc s_exp n_info sizeOf
    | Cil.SizeOfE e ->
      let sizeOfE, here =
        Val.of_itv (try CilHelper.byteSizeOf (Cil.typeOf e) |> Itv.of_int with _ -> Itv.pos), [%here] in
      Val.modify_footprints here loc s_exp n_info sizeOfE
    | Cil.SizeOfStr s ->
      let sizeOfStr, here = Val.of_itv (Itv.of_int (String.length s + 1)), [%here] in
      Val.modify_footprints here loc s_exp n_info sizeOfStr
    | Cil.AlignOf t ->
      let alignOf, here = Val.of_itv (Itv.of_int (Cil.alignOf_int t)), [%here] in
      Val.modify_footprints here loc s_exp n_info alignOf
    (* TODO: type information is required for precise semantics of AlignOfE.  *)
    | Cil.AlignOfE _ -> Val.modify_footprints [%here] loc s_exp n_info (Val.of_itv Itv.top)
    | Cil.UnOp (u, e, _) ->
      eval_uop spec u (eval ~spec pid e mem loc n_info) loc s_exp n_info
    | Cil.BinOp (b, e1, e2, _) ->
      let v1 = eval ~spec pid e1 mem loc n_info in
      let v2 = eval ~spec pid e2 mem loc n_info in
      eval_bop spec b v1 v2 loc s_exp n_info
    | Cil.Question (e1, e2, e3, _) ->
      let i1 = Val.itv_of_val (eval ~spec pid e1 mem loc n_info) in
      if Itv.is_bot i1 then
        Val.modify_footprints [%here] loc s_exp n_info Val.bot
      else if Itv.eq (Itv.of_int 0) i1 then
        Val.modify_footprints [%here] loc s_exp n_info (eval ~spec pid e3 mem loc n_info)
      else if not (Itv.le (Itv.of_int 0) i1) then
        Val.modify_footprints [%here] loc s_exp n_info (eval ~spec pid e2 mem loc n_info)
      else
        let v, here = Val.join (eval ~spec pid e2 mem loc n_info) (eval ~spec pid e3 mem loc n_info ), [%here] in
        Val.modify_footprints here loc s_exp n_info v
    | Cil.CastE (t, e) ->
      let v = eval ~spec pid e mem loc n_info in
      (try Val.cast (Cil.typeOf e) t v (loc, (Cil.CastE (t, e))) n_info with _ -> Val.modify_footprints [%here] loc s_exp n_info v)
    | Cil.AddrOf l ->
      let powloc, lv_fp, fp_opt = eval_lv_with_footprint ~spec pid l mem loc ~n_info in
      Val.modify_footprints'''' [%here] lv_fp fp_opt loc s_exp n_info (Val.of_pow_loc powloc)
    | Cil.AddrOfLabel _ ->
      invalid_arg "itvSem.ml:eval AddrOfLabel mem. \
                   Analysis does not support label values."
    | Cil.StartOf l ->
      let powloc, lv_fp, fp_opt = eval_lv_with_footprint ~spec pid l mem loc ~n_info in
      Val.modify_footprints'''' [%here] lv_fp fp_opt loc s_exp n_info (lookup powloc mem)

let eval_lv ?(spec=Spec.empty) pid lv mem loc ~n_info =
  let (lv, _, _) = (eval_lv_with_footprint ~spec pid lv mem loc ~n_info) in
  lv

let eval_list : Spec.t -> Proc.t -> Cil.exp list -> Mem.t -> Cil.location -> n_info:string -> Val.t list
= fun spec pid exps mem loc ~n_info -> List.map (fun e -> eval ~spec pid e mem loc n_info) exps

let eval_array_alloc ?(spec=Spec.empty) : Node.t -> Cil.exp -> bool -> Mem.t -> Cil.location -> n_info:string -> Val.t
  = fun node e is_static mem loc ~n_info ->
  let pid = Node.get_pid node in
  let allocsite = Allocsite.allocsite_of_node node in
  let o = Itv.of_int 0 in
  let sz = Val.itv_of_val (eval ~spec pid e mem loc n_info) in
  (* NOTE: stride is always one when allocating memory. *)
  let st = Itv.of_int 1 in
  let np = Itv.nat in
  let pow_loc = if is_static then PowLoc.bot else PowLoc.singleton Loc.null in
  let array = ArrayBlk.make allocsite o sz st np in
  Val.join (Val.of_pow_loc pow_loc) (Val.of_array array)

let eval_struct_alloc : PowLoc.t -> Cil.compinfo -> Cil.location -> exp:ExpArg.t -> n_info:string -> Val.t
  = fun lv comp loc ~exp ~n_info ->
    StructBlk.make lv comp |> Val.of_struct |> Val.modify_footprints [%here] loc exp ~n_info

let eval_string_alloc : Node.t -> string -> Mem.t -> Cil.location -> n_info:string -> Val.t
  = fun node s mem loc ~n_info ->
    let s_exp =  ExpArg.Exp (Cil.Const (Cil.CStr s)) in
    let allocsite = Allocsite.allocsite_of_string node in
    let o = Itv.of_int 0 in
    let sz = Itv.of_int (String.length s + 1) in
    let st = Itv.of_int 1 in
    let np = Itv.of_int (String.length s) in
    let array = ArrayBlk.make allocsite o sz st np in
    Val.of_array array |> Val.modify_footprints [%here] loc s_exp ~n_info


let eval_string : string -> Val.t = fun s ->
  Val.of_itv Itv.nat

(* ****************************** *
 * Semantic functions for pruning *
 * ****************************** *)

let rec prune_simple : update_mode -> Spec.t -> Global.t -> Proc.t -> exp -> Mem.t ->
  Cil.location -> n_info:string -> Mem.t
= fun mode spec global pid cond mem loc ~n_info ->
  match cond with
  | BinOp (op, Lval x, e, t)
    when op = Lt || op = Gt || op = Le || op = Ge || op = Eq || op = Ne ->
    let x_lv = eval_lv ~spec pid x mem loc ~n_info in
    if PowLoc.cardinal x_lv = 1 then
      let x_v = lookup x_lv mem in
      let e_v = eval ~spec pid e mem loc n_info |> Val.itv_of_val in
      let x_itv = Val.itv_of_val x_v in
      let x_ploc = Val.pow_loc_of_val x_v in
      let x_itv = Itv.prune op x_itv e_v in
      let x_ploc = PowLoc.prune op x_ploc e in
      let x_pruned = Val.make (x_itv, x_ploc, Val.array_of_val x_v, Val.struct_of_val x_v,
                               Val.pow_proc_of_val x_v, Val.footprints_of_val x_v) in
      update mode spec global x_lv x_pruned mem
    else mem
  | BinOp (op, e1, e2, _) when op = LAnd || op = LOr ->
    let mem1 = prune_simple mode spec global pid e1 mem loc n_info in
    let mem2 = prune_simple mode spec global pid e2 mem loc n_info in
    if op = LAnd then Mem.meet mem1 mem2 else Mem.join mem1 mem2
  | UnOp (LNot, Lval x, _) ->
    let x_lv = eval_lv ~spec pid x mem loc ~n_info in
    if PowLoc.cardinal x_lv = 1 then
      let x_v = lookup x_lv mem in
      let x_itv = Val.itv_of_val x_v in
      let e_v = Itv.zero in
      let x_itv = Itv.meet x_itv e_v in
      let x_pruned = Val.modify_itv x_itv x_v in
      update mode spec global x_lv x_pruned mem
    else mem
  | Lval x ->
    let x_lv = eval_lv ~spec pid x mem loc ~n_info in
    if PowLoc.cardinal x_lv = 1 then
      let x_v = lookup x_lv mem in
      let x_itv = Val.itv_of_val x_v in
      let pos_x = Itv.meet x_itv Itv.pos in
      let neg_x = Itv.meet x_itv Itv.neg in
      let x_itv = Itv.join pos_x neg_x in
      let x_pruned = Val.modify_itv x_itv x_v in
      update mode spec global x_lv x_pruned mem
    else mem
  | _ -> mem

let prune : update_mode -> Spec.t -> Global.t -> Proc.t -> exp -> Mem.t -> Cil.location -> n_info:string -> Mem.t
= fun mode spec global pid cond mem loc ~n_info ->
  match CilHelper.make_cond_simple cond with
  | None -> mem
  | Some cond_simple -> prune_simple mode spec global pid cond_simple mem loc n_info

(* ******************************* *
 * Semantic functions for commands *
 * ******************************* *)
let sparrow_print spec pid exps mem loc n_info =
  if !Options.verbose < 1 then ()
  else
    let vs = eval_list spec pid exps mem loc n_info in
    let vs_str = string_of_list Val.to_string vs in
    let exps_str = string_of_list CilHelper.s_exp exps in
    prerr_endline
      ("sparrow_print (" ^ exps_str ^ " @ " ^ CilHelper.s_location loc ^ ") : "
       ^ vs_str)

let sparrow_dump mem loc =
  if !Options.verbose < 1 then ()
  else
    prerr_endline
      ("sparrow_dump (" ^ CilHelper.s_location loc ^ ") : \n"
       ^ Mem.to_string mem)

let model_alloc_one mode spec pid (lvo, exps) f (mem, global) loc n_info =
  match lvo with
    None -> (mem, global)
  | Some lv ->
    let allocsite = Allocsite.allocsite_of_ext (Some f.vname) in
    let arr_val, here = Val.of_array (ArrayBlk.make allocsite Itv.zero Itv.one Itv.one Itv.nat), [%here] in
    let arr_val = Val.modify_footprints here loc (Fun (f.vname, exps)) n_info arr_val in
    let ext_loc = PowLoc.singleton (Loc.of_allocsite allocsite) in
    let ext_val, here = Val.itv_top, [%here] in
    let ext_val = Val.modify_footprints here loc (Fun (f.vname, exps)) ~n_info ext_val in
    let mem = update mode spec global (eval_lv ~spec pid lv mem loc ~n_info) arr_val mem in
    let mem = update mode spec global ext_loc ext_val mem in
    (mem,global)

let model_realloc mode spec node (lvo, exps) (mem, global) loc =
  let pid = Node.get_pid node in
  let n_info = InterCfg.Node.to_string node in
  match lvo with
  | Some lv ->
    begin
      match exps with
      | _::size::_ ->
        let v = eval_array_alloc ~spec node size false mem loc ~n_info
                |> Val.modify_footprints [%here] loc (Fun ("realloc", exps)) ~n_info in
        (update mode spec global (eval_lv ~spec pid lv mem loc ~n_info) v mem, global)
      | _ -> raise (Failure "Error: arguments of realloc are not given")
    end
  | _ -> (mem,global)

let model_calloc mode spec node (lvo, exps) (mem, global) loc =
  let pid = Node.get_pid node in
  let n_info = InterCfg.Node.to_string node in
  match lvo with
  | Some lv ->
    begin
      match exps with
      | n::size::_ ->
        let new_size = Cil.BinOp (Cil.Mult, n, size, Cil.uintType) in
        let v = eval_array_alloc ~spec node new_size false mem loc ~n_info
                |> Val.modify_footprints [%here] loc (Fun ("calloc", exps)) ~n_info in
        (update mode spec global (eval_lv ~spec pid lv mem loc ~n_info) v mem, global)
      | _ -> raise (Failure "Error: arguments of realloc are not given")
    end
  | _ -> (mem,global)

let model_scanf mode spec pid exps (mem, global) loc n_info =
  let modify_fp here ?(exp=(ExpArg.Fun("scanf", exps))) v = Val.modify_footprints here loc exp n_info v in
  match exps with
    _::t ->
      List.fold_left (fun (mem, global) e ->
          match e with
              Cil.AddrOf lv ->
              let mem = update mode spec global (eval_lv ~spec pid lv mem loc ~n_info) (Val.itv_top |> modify_fp [%here]) mem in
              (mem, global)
          | _ -> (mem,global)) (mem,global) t
  | _ -> (mem, global)

let model_strdup mode spec node (lvo, exps) (mem, global) loc' =
  let pid = Node.get_pid node in
  let n_info = InterCfg.Node.to_string node in
  let modify_fp here ?(exp=(ExpArg.Fun("strdup", exps))) v = Val.modify_footprints here loc' exp n_info v in
  match (lvo, exps) with
  | (Some lv, str::_) ->
    let allocsite = Allocsite.allocsite_of_node node in
    let str_val = eval ~spec pid str mem loc' n_info |> ItvDom.Val.array_of_val in
    let size = ArrayBlk.sizeof str_val in
    let null_pos = ArrayBlk.nullof str_val in
    let allocsites = ArrayBlk.pow_loc_of_array str_val in
    let offset = Itv.zero in
    let arr_val = ArrayBlk.make allocsite Itv.zero (Itv.minus size offset) Itv.one null_pos in
    let loc = PowLoc.singleton (Loc.of_allocsite allocsite) in
    let v = Val.join (Val.of_array arr_val) (Val.of_pow_loc loc) |> modify_fp [%here] in
    let mem = update mode spec global (eval_lv ~spec pid lv mem loc' ~n_info) v mem in
    let mem = update mode spec global loc (lookup allocsites mem |> modify_fp [%here]) mem in
    (mem,global)
  | _ -> (mem,global)

let model_input mode spec pid (lvo, exps) (mem, global) loc n_info =
  let modify_fp here ?(exp=(ExpArg.Fun("getenv", exps))) v = Val.modify_footprints here loc exp n_info v in
  match lvo with
    Some lv ->
      let allocsite = Allocsite.allocsite_of_ext None in
      let ext_v = Val.external_value allocsite |> modify_fp [%here] in
      let ext_loc = PowLoc.singleton (Loc.of_allocsite allocsite) in
      let mem = update mode spec global (eval_lv ~spec pid lv mem loc ~n_info) ext_v mem in
      let mem = update mode spec global ext_loc (Val.itv_top |> modify_fp [%here]) mem in
        (mem,global)
  | _ -> (mem,global)

let model_assign mode spec pid (lvo,exps) (mem, global) loc n_info =
  let modify_fp here ?(exp=(ExpArg.Fun("gettext", exps))) v = Val.modify_footprints here loc exp n_info v in
  match (lvo,exps) with
    (Some lv, e::_) ->
    (update mode spec global (eval_lv ~spec pid lv mem loc ~n_info) (eval ~spec pid e mem loc n_info |> modify_fp [%here]) mem, global)
  | (_, _) -> (mem,global)


let model_strlen mode spec pid (lvo, exps) (mem, global) loc n_info =
  match (lvo, exps) with
  | (Some lv, str::_) ->
    let str_val = eval ~spec pid str mem loc n_info in
    let null_pos = ArrayBlk.nullof (ItvDom.Val.array_of_val str_val) in
    let itv, here = (Itv.meet Itv.nat null_pos), [%here] in
    let v = Val.modify_footprints' here (Val.footprints_of_val str_val) loc (ExpArg.Fun("strlen", exps)) n_info (Val.of_itv itv) in
    let lv = eval_lv ~spec pid lv mem loc ~n_info in
    (update mode spec global lv v mem, global)
  | _ -> (mem,global)

let rec model_fgets mode spec pid (lvo, exps) (mem, global) loc n_info =
  let modify_fp here ?(exp=(ExpArg.Fun("fgets", exps))) v = Val.modify_footprints here loc exp n_info v in
  match (lvo, exps) with
  | (_, Lval buf::size::_) | (_, StartOf buf::size::_) ->
    let size_itv = eval ~spec pid size mem loc n_info |> ItvDom.Val.itv_of_val in
    let buf_lv = eval_lv ~spec pid buf mem loc ~n_info in
    let buf_arr = lookup buf_lv mem |> ItvDom.Val.array_of_val in
    let allocsites = ArrayBlk.pow_loc_of_array buf_arr in
    let buf_val = ArrayBlk.set_null_pos buf_arr (Itv.join Itv.zero size_itv) |> ItvDom.Val.of_array |> modify_fp [%here] in
     (* (update mode spec global buf_lv buf_val mem, global) *)
    mem
    |> update mode spec global buf_lv buf_val
    |> update mode spec global allocsites (Val.itv_top |> modify_fp [%here])
    |> (fun mem -> (mem, global))
  | (_, CastE (_, buf)::size::e) -> model_fgets mode spec pid (lvo, buf::size::e) (mem, global) loc n_info
  | _ -> (mem,global)

let rec model_sprintf mode spec pid (lvo, exps) (mem, global) loc n_info  =
  let modify_fp here ?(exp=(ExpArg.Fun("sprintf", exps))) v = Val.modify_footprints here loc exp n_info v in
  match exps with
  | Lval buf::str::[] | StartOf buf::str::[] ->  (* format string *)
    let str_val = eval ~spec pid str mem loc n_info |> ItvDom.Val.array_of_val in
    let (arrays, null_pos) = (ArrayBlk.pow_loc_of_array str_val, ArrayBlk.nullof str_val) in
    let buf_lv = eval_lv ~spec pid buf mem loc ~n_info in
    let buf_arr = lookup buf_lv mem |> ItvDom.Val.array_of_val in
    let allocsites = ArrayBlk.pow_loc_of_array buf_arr in
    let buf_val = ArrayBlk.set_null_pos buf_arr null_pos |> ItvDom.Val.of_array |> modify_fp [%here] in
    mem
    |> update mode spec global buf_lv buf_val
    |> update mode spec global allocsites (lookup arrays mem)
    |> (match lvo with 
        | Some lv ->
          update mode spec global (eval_lv ~spec pid lv mem loc ~n_info) (Val.of_itv null_pos |> modify_fp [%here])
        | _ -> id)
    |> (fun mem -> (mem, global))
  | CastE (_, buf)::str::[]
  | buf::CastE (_, str)::[] -> model_sprintf mode spec pid (lvo, buf::str::[]) (mem, global) loc n_info
  | _ ->
    begin
      match lvo with
        Some lv ->
        (update mode spec global (eval_lv ~spec pid lv mem loc ~n_info) (Val.of_itv Itv.nat |> modify_fp [%here]) mem, global)
      | _ -> (mem,global)
    end

(* argc, argv *)
let sparrow_arg mode spec pid exps (mem,global) loc n_info =
  let modify_fp here ?(exp=(ExpArg.Fun("sparrow_arg", exps))) v = Val.modify_footprints here loc exp n_info v in
  match exps with
    (Cil.Lval argc)::(Cil.Lval argv)::_ ->
      let argv_a = Allocsite.allocsite_of_ext (Some "argv") in
      let argv_v = Val.of_array (ArrayBlk.input argv_a) |> modify_fp [%here] ~exp:(Exp (Cil.Const (Cil.CStr "argv"))) in
      let arg_a = Allocsite.allocsite_of_ext (Some "arg") in
      let arg_v = Val.of_array (ArrayBlk.input arg_a) |> modify_fp [%here] ~exp:(Exp (Cil.Const (Cil.CStr "arg"))) in
      (update mode spec global (eval_lv ~spec pid argc mem loc ~n_info) (Val.of_itv Itv.pos |> modify_fp [%here]) mem
      |> update mode spec global (eval_lv ~spec pid argv mem loc ~n_info) argv_v
      |> update mode spec global (PowLoc.singleton (Loc.of_allocsite argv_a)) arg_v
      |> update mode spec global (PowLoc.singleton (Loc.of_allocsite arg_a)) (Val.of_itv Itv.top |> modify_fp [%here]), global)
  | _ -> (mem,global)

(* optind, optarg *)
let sparrow_opt mode spec pid exps (mem,global) loc n_info =
  let modify_fp here v = Val.modify_footprints here loc (Fun("sparrow_opt", exps)) n_info v in
  match exps with
    (Cil.Lval optind)::(Cil.Lval optarg)::_ ->
      let arg_a = Allocsite.allocsite_of_ext (Some "arg") in
      let arg_v = Val.of_array (ArrayBlk.input arg_a) |> modify_fp [%here] in
      (update mode spec global (eval_lv ~spec pid optind mem loc ~n_info) ((Val.of_itv Itv.nat) |> modify_fp [%here]) mem
      |> update mode spec global (eval_lv ~spec pid optarg mem loc ~n_info) arg_v
      |> update mode spec global (PowLoc.singleton (Loc.of_allocsite arg_a)) ((Val.of_itv Itv.top) |> modify_fp [%here]), global)
  | _ -> (mem,global)

let model_unknown mode spec node pid lvo f exps (mem, global) loc =
  let n_info = InterCfg.Node.to_string node in
  let modify_fp here v = Val.modify_footprints here loc (Fun(f.vname, exps)) n_info v in
  match lvo with
    None -> (mem, global)
  | Some lv when Cil.isArithmeticType (Cil.unrollTypeDeep (Cil.typeOfLval lv)) ->
      let ext_v = if CilHelper.is_unsigned (Cil.unrollTypeDeep (Cil.typeOfLval lv)) then
                    Val.of_itv Itv.nat |> modify_fp [%here]
                  else Val.of_itv Itv.top |> modify_fp [%here]
      in
      let lv = eval_lv ~spec pid lv mem loc ~n_info in
      let mem = update mode spec global lv ext_v mem in
      (mem,global)
  | Some lv ->
      let allocsite = Allocsite.allocsite_of_ext (Some f.vname) in
      let ext_v = ArrayBlk.extern allocsite |> ArrayBlk.cast_array (Cil.typeOfLval lv) |> Val.of_array |> modify_fp [%here] in
      let ext_loc = PowLoc.singleton (Loc.of_allocsite allocsite) in
      let lv = eval_lv ~spec pid lv mem loc ~n_info in
      let mem = update mode spec global lv ext_v mem in
      let mem = update mode spec global ext_loc (Val.itv_top|> modify_fp [%here]) mem in
      (mem,global)

let model_memcpy mode spec pid (lvo, exps) (mem, global) loc n_info =
  let modify_fp here ?(exp=ExpArg.Fun("memcpy", exps)) v = Val.modify_footprints here loc exp n_info v in
  match (lvo, exps) with
    Some lv, dst::src::_ ->
    let (src_v, dst_v) = tuple mem
                         |> Tuple2.map (fun mem -> eval ~spec pid src mem loc n_info) (fun mem -> eval ~spec pid dst mem loc n_info)
                         |> Tuple2.map (fun src_v -> modify_fp [%here] ~exp:(ExpArg.Exp src) src_v) (fun dst_v -> modify_fp [%here] ~exp:(ExpArg.Exp dst) dst_v) in
    let (src_l, dst_l) = (src_v, dst_v)
                         |> Tuple2.mapn Val.array_of_val
                         |> Tuple2.mapn ArrayBlk.pow_loc_of_array in
    let lv = eval_lv ~spec pid lv mem loc ~n_info in
    mem
    |> update mode spec global dst_l (lookup src_l mem |> modify_fp [%here])
    |> update mode spec global lv dst_v
    |> (fun mem -> (mem, global))
  | _, _ -> (mem, global)

let model_getpwent mode spec node pid (lvo, exps) f (mem,global) loc =
  let n_info = InterCfg.Node.to_string node in
  let modify_fp here ?(exp=ExpArg.Fun (f.vname, exps)) v = Val.modify_footprints here loc exp n_info v in
  match lvo, f.vtype with
    Some lv, Cil.TFun ((Cil.TPtr ((Cil.TComp (comp, _) as elem_t), _) as ptr_t), _, _, _) ->
      let struct_loc = eval_lv ~spec pid lv mem loc ~n_info in
      let struct_v = eval_array_alloc ~spec node (Cil.SizeOf elem_t) false mem loc ~n_info
                     |> modify_fp [%here]
                     |> fun v -> Val.cast ptr_t (Cil.typeOfLval lv) v (loc, (Cil.Const (Cil.CStr "temp"))) n_info in
      let field_loc = ArrayBlk.append_field (Val.array_of_val struct_v) (List.find (fun f -> f.fname ="pw_name") comp.cfields) in
      let allocsite = Allocsite.allocsite_of_ext (Some "getpwent.pw_name") in
      let ext_v = ArrayBlk.input allocsite |> Val.of_array |> modify_fp [%here] ~exp:(ExpArg.Exp (Cil.Const (Cil.CStr "pw_name"))) in
      let ext_loc = PowLoc.singleton (Loc.of_allocsite allocsite) in
      let mem = update mode spec global struct_loc struct_v mem
              |> update mode spec global field_loc ext_v
              |> update mode spec global ext_loc (Val.itv_top |> modify_fp [%here]) in
      (mem, global)
  | _ -> (mem, global)

let rec model_strcpy mode spec node pid es (mem, global) loc =
  let n_info = InterCfg.Node.to_string node in
  match es with
    (CastE (_, e))::t -> model_strcpy mode spec node pid (e::t) (mem,global) loc
  | dst::(CastE(_, e))::[] -> model_strcpy mode spec node pid (dst::e::[]) (mem,global) loc
  | (Lval dst)::(Lval src)::[] | (StartOf dst)::(StartOf src)::[]
  | (Lval dst)::(StartOf src)::[] | (StartOf dst)::(Lval src)::[] ->
      let src_v = lookup (eval_lv ~spec pid src mem loc ~n_info) mem in
      let src_arr, src_fp  = Val.array_of_val src_v, Val.footprints_of_val src_v in
      let dst_v = lookup (eval_lv ~spec pid dst mem loc ~n_info) mem in
      let dst_arr, dst_fp = Val.array_of_val dst_v, Val.footprints_of_val dst_v in
      let np = ArrayBlk.nullof src_arr in
      let newv, here = Val.of_array (ArrayBlk.set_null_pos dst_arr np), [%here] in
      let newv = Val.modify_footprints'' here (src_fp :: dst_fp :: []) loc (Fun ("strcpy", es)) n_info newv in
      let mem = mem |> update mode spec global (eval_lv ~spec pid dst mem loc ~n_info) newv in
      (mem, global)
  | _ -> (mem, global)

let rec model_strncpy mode spec node pid es (mem, global) loc =
  let n_info = InterCfg.Node.to_string node in
  match es with
    CastE (_, e)::t -> model_strncpy mode spec node pid (e::t) (mem, global) loc
  | (Lval dst)::_::size::_
  | (StartOf dst)::_::size::_ ->
      let arr = Val.array_of_val (lookup (eval_lv ~spec pid dst mem loc ~n_info) mem) in
      let sz = Val.itv_of_val (eval ~spec pid size mem loc n_info) in
      let np = Itv.join Itv.zero (Itv.minus sz Itv.one) in
      let newv = Val.of_array (ArrayBlk.set_null_pos arr np) |> Val.modify_footprints [%here] loc (Fun ("strncpy", es)) ~n_info in
      let mem = mem |> update mode spec global (eval_lv ~spec pid dst mem loc ~n_info) newv in
      (mem, global)
  | _ -> (mem,global)

let rec model_strcat mode spec node pid es (mem, global) loc =
  let n_info = InterCfg.Node.to_string node in
  match es with
    (CastE (_, e))::t -> model_strcat mode spec node pid (e::t) (mem,global) loc
  | dst::(CastE(_, e))::[] -> model_strcat mode spec node pid (dst::e::[]) (mem,global) loc
  | (Lval dst)::(Lval src)::[] | (StartOf dst)::(StartOf src)::[]
  | (Lval dst)::(StartOf src)::[] | (StartOf dst)::(Lval src)::[] ->
      let src_arr = Val.array_of_val (lookup (eval_lv ~spec pid src mem loc ~n_info) mem) in
      let dst_arr = Val.array_of_val (lookup (eval_lv ~spec pid dst mem loc ~n_info) mem) in
      let np = ArrayBlk.nullof src_arr in
      let newv = Val.of_array (ArrayBlk.plus_null_pos dst_arr np) |> Val.modify_footprints [%here] loc (Fun ("strcat", es)) ~n_info in
      let mem = mem |> update mode spec global (eval_lv ~spec pid dst mem loc ~n_info) newv in
      (mem, global)
  | _ -> (mem, global)

let rec model_strchr mode spec node pid (lvo, exps) (mem, global) loc =
  let n_info = InterCfg.Node.to_string node in
  match lvo, exps with
    Some _, (CastE (_, e))::t -> model_strchr mode spec node pid (lvo, e::t) (mem,global) loc
  | Some lv, (Lval str)::_ | Some lv, (StartOf str)::_ ->
      let str_arr = Val.array_of_val (lookup (eval_lv ~spec pid str mem loc ~n_info) mem) in
      let np = ArrayBlk.nullof str_arr in
      let newv = Val.of_array (ArrayBlk.plus_offset str_arr np) |> Val.modify_footprints [%here] loc (Fun ("strchr", exps)) ~n_info in
      let mem = mem |> update mode spec global (eval_lv ~spec pid lv mem loc ~n_info) newv in
      (mem, global)
  | _, _ -> (mem, global)

let sparrow_array_init mode spec node pid exps (mem, global) loc =
  let n_info = InterCfg.Node.to_string node in
  let modify_fp here ?(exp=ExpArg.Fun ("sparrow_array_init", exps)) v = Val.modify_footprints here loc exp n_info v in
  match List.nth exps 0, List.nth exps 1 with
  | arr, Cil.Const (Cil.CInt64 (_, _, _)) ->
      let lv = eval ~spec pid arr mem loc n_info |> Val.array_of_val |> ArrayBlk.pow_loc_of_array in
      let v = List.fold_left (fun v e -> Val.join (eval ~spec pid e mem loc n_info) v) Val.bot (List.tl exps) |> modify_fp [%here] in
      (update mode spec global lv v mem, global)
  | arr, Cil.Const (Cil.CStr s) ->
      let lv = eval ~spec pid arr mem loc n_info |> Val.array_of_val |> ArrayBlk.pow_loc_of_array in
      let v, here = List.fold_left (fun v e ->
          match e with
            Cil.Const (Cil.CStr s) ->
              Val.join (eval_string_alloc node s mem loc n_info) v
          | _ -> v) Val.bot (List.tl exps), [%here]
      in
      (update mode spec global lv (v |> modify_fp here) mem, global)
  | arr, _ ->
    let getLval e =
      match e with
      | Cil.Lval l -> eval_lv ~spec pid l mem loc ~n_info
      | _ -> raise (Failure "Error: not Lval ")
    in
    let v = eval ~spec pid arr mem loc n_info |> modify_fp [%here] in
    (update mode spec global (getLval arr) v mem, global)

let mem_alloc_libs = ["__ctype_b_loc"; "initscr"; "newwin"; "localtime"; "__errno_location"; "opendir"; "readdir"]
let scaffolded_functions mode spec node pid (lvo,f,exps) (mem, global) loc =
  let n_info = InterCfg.Node.to_string node in
  if !Options.scaffold then
    match f.vname with
    | "fgets" -> model_fgets mode spec pid (lvo, exps) (mem, global) loc n_info
    | "sprintf" -> model_sprintf mode spec pid (lvo, exps) (mem, global) loc n_info
    | "scanf" -> model_scanf mode spec pid exps (mem, global) loc n_info
    | "getenv" -> model_input mode spec pid (lvo, exps) (mem, global) loc n_info
    | "strdup" -> model_strdup mode spec node (lvo, exps) (mem, global) loc 
    | "gettext" -> model_assign mode spec pid (lvo, exps) (mem, global) loc n_info
    | "memcpy" -> model_memcpy mode spec pid (lvo, exps) (mem, global) loc n_info
    | "getpwent" -> model_getpwent mode spec node pid (lvo, exps) f (mem,global) loc
    | "strcpy" -> model_strcpy mode spec node pid exps (mem, global) loc
    | "strncpy" -> model_strncpy mode spec node pid exps (mem, global) loc
    | "strcat" -> model_strcat mode spec node pid exps (mem, global) loc
    | "strchr" | "strrchr" -> model_strchr mode spec node pid (lvo, exps) (mem, global) loc
    | s when List.mem s mem_alloc_libs -> model_alloc_one mode spec pid (lvo, exps) f (mem, global) loc n_info
    | _ -> model_unknown mode spec node pid lvo f exps (mem, global) loc
  else
    model_unknown mode spec node pid lvo f exps (mem, global) loc

let handle_undefined_functions mode spec node pid (lvo,f,exps) (mem,global) loc =
  let n_info = InterCfg.Node.to_string node in
  match f.vname with
  | "sparrow_arg" -> sparrow_arg mode spec pid exps (mem,global) loc n_info
  | "sparrow_opt" -> sparrow_opt mode spec pid exps (mem,global) loc n_info
  | "sparrow_print" -> sparrow_print spec pid exps mem loc n_info; (mem,global)
  | "sparrow_dump" -> sparrow_dump mem loc; (mem,global)
  | "sparrow_assume" -> (prune mode spec global pid (List.hd exps) mem loc n_info, global)
  | "sparrow_array_init" -> sparrow_array_init mode spec node pid exps (mem, global) loc
  | "strlen" -> model_strlen mode spec pid (lvo, exps) (mem, global) loc n_info
  | "realloc" -> model_realloc mode spec node (lvo, exps) (mem, global) loc
  | "calloc" -> model_calloc mode spec node (lvo, exps) (mem, global) loc
  | _ -> scaffolded_functions mode spec node pid (lvo, f, exps) (mem, global) loc

let bind_lvar : update_mode -> Spec.t -> Global.t -> Loc.t -> Val.t -> Mem.t -> Mem.t
= fun mode spec global lvar v mem ->
  let l = PowLoc.singleton lvar in
  update mode spec global l v mem

let bind_arg_ids : update_mode -> Spec.t -> Global.t -> Val.t list -> Loc.t list -> Mem.t -> Mem.t
= fun mode spec global vs arg_ids mem ->
  list_fold2 (bind_lvar mode spec global) arg_ids vs mem

(* Binds a list of values to a set of argument lists.  If |args_set|
    > 1, the argument binding does weak update. *)
let bind_arg_lvars_set : update_mode -> Spec.t -> Global.t -> (Loc.t list) BatSet.t -> Val.t list -> Mem.t -> Mem.t
= fun mode spec global arg_ids_set vs mem ->
  let is_same_length l = List.length l = List.length vs in
  let arg_ids_set = BatSet.filter is_same_length arg_ids_set in
  let mode = if BatSet.cardinal arg_ids_set > 1 then AbsSem.Weak else mode in
  BatSet.fold (bind_arg_ids mode spec global vs) arg_ids_set mem

(* Default update option is weak update. *)
let run : update_mode -> Spec.t -> Node.t -> Mem.t * Global.t -> Mem.t * Global.t
= fun mode spec node (mem, global) ->
  let pid = Node.get_pid node in
  let n_info = InterCfg.Node.to_string node in
  let modify_fp loc s_exp here v = Val.modify_footprints here loc s_exp n_info v in
  match InterCfg.cmdof global.icfg node with
  | IntraCfg.Cmd.Cset (l, e, loc) ->
    (update mode spec global (eval_lv ~spec pid l mem loc ~n_info) (eval ~spec pid e mem loc n_info) mem, global)
  | IntraCfg.Cmd.Cexternal (l, loc) ->
    let exp_arg = ExpArg.Exp (Cil.Const (Cil.CStr "external")) in
    (match Cil.typeOfLval l with
       Cil.TInt (_, _) | Cil.TFloat (_, _) ->
         let ext_v = Val.of_itv Itv.top |> modify_fp loc exp_arg [%here] in
         let mem = update mode spec global (eval_lv ~spec pid l mem loc ~n_info) ext_v mem in
         (mem,global)
     | _ ->
       let allocsite = Allocsite.allocsite_of_ext None in
       let ext_v = Val.external_value allocsite |> modify_fp loc exp_arg [%here] in
       let ext_loc = PowLoc.singleton (Loc.of_allocsite allocsite) in
       let mem = update mode spec global (eval_lv ~spec pid l mem loc ~n_info) ext_v mem in
       let mem = update mode spec global ext_loc ext_v mem in
        (mem,global))
  | IntraCfg.Cmd.Calloc (l, IntraCfg.Cmd.Array e, is_static, loc) ->
    let v = eval_array_alloc ~spec node e is_static mem loc ~n_info |> modify_fp loc (Fun ("array_alloc", [e])) [%here] in
    (update mode spec global (eval_lv ~spec pid l mem loc ~n_info) v mem, global)
  | IntraCfg.Cmd.Calloc (l, IntraCfg.Cmd.Struct s, is_static, loc) ->
    let lv = eval_lv ~spec pid l mem loc ~n_info in
    let v = eval_struct_alloc lv s loc (Fun ("struct_alloc", [Cil.Const (Cil.CStr (s.cname))]))  n_info in
    (update mode spec global lv v mem, global)
  | IntraCfg.Cmd.Csalloc (l, s, loc) ->
    let str_loc =
      Allocsite.allocsite_of_string node
      |> Loc.of_allocsite |> PowLoc.singleton
    in
    mem
    |> update mode spec global (eval_lv ~spec pid l mem loc ~n_info) (eval_string_alloc node s mem loc n_info)
    |> update mode spec global str_loc (eval_string s |> modify_fp loc (Fun ("eval_string", [Cil.Const (Cil.CStr s)])) [%here])
    |> (fun mem -> (mem, global))
  | IntraCfg.Cmd.Cfalloc (l, fd, loc) ->
    let clos = Val.of_pow_proc (PowProc.singleton fd.svar.vname) in
    (update mode spec global (eval_lv ~spec pid l mem loc ~n_info) clos mem, global)
  | IntraCfg.Cmd.Cassume (e, loc) ->
    let _ : ItvDom.Val.t = eval ~spec pid e mem loc n_info in (* for inspection *)
    (prune mode spec global pid e mem loc n_info, global)
  | IntraCfg.Cmd.Ccall (lvo, Cil.Lval (Cil.Var f, Cil.NoOffset), arg_exps, loc)
    when Global.is_undef f.vname global -> (* undefined library functions *)
    if BatSet.mem ((CilHelper.s_location loc)^":"^f.vname) spec.Spec.unsound_lib then (mem,global)
    else
      let _ : ItvDom.Val.t list = eval_list spec pid arg_exps mem loc n_info in (* for inspection *)
      handle_undefined_functions mode spec node pid (lvo,f,arg_exps) (mem,global) loc
  | IntraCfg.Cmd.Ccall (lvo, f, arg_exps, loc) -> (* user functions *)
    let fs = Val.pow_proc_of_val (eval ~spec pid f mem loc n_info) in
    if PowProc.eq fs PowProc.bot then (mem, global)
    else
      let arg_lvars_of_proc f acc =
        let args = InterCfg.argsof global.icfg f in
        let lvars = List.map (fun x -> Loc.of_lvar f x.Cil.vname x.Cil.vtype) args in
        BatSet.add lvars acc in
      let arg_lvars_set = PowProc.fold arg_lvars_of_proc fs BatSet.empty in
      let arg_vals = eval_list spec pid arg_exps mem loc n_info in
      let dump =
         match lvo with
         | None -> global.dump
         | Some lv ->
           let retvars_of_proc f acc =
             let ret = Loc.return_var f (Cil.typeOfLval lv) in
             PowLoc.add ret acc in
           let retvar_set = PowProc.fold retvars_of_proc fs PowLoc.empty in
           let _ = Mem.lookup retvar_set mem in
           PowProc.fold (fun f d ->
              Dump.weak_add f (eval_lv ~spec pid lv mem loc ~n_info) d
           ) fs global.dump in
      let mem = bind_arg_lvars_set mode spec global arg_lvars_set arg_vals mem in
      (mem, { global with dump })
  | IntraCfg.Cmd.Creturn (ret_opt, loc) ->
      (match ret_opt with
      | None -> mem
      | Some e ->
        update Weak spec global (Loc.return_var pid (Cil.typeOf e) |> PowLoc.singleton) (eval ~spec pid e mem loc n_info) mem)
      |> (fun mem -> (mem, global))
  | IntraCfg.Cmd.Cskip when InterCfg.is_returnnode node global.icfg ->
    let callnode = InterCfg.callof node global.icfg in
    (match InterCfg.cmdof global.icfg callnode with
       IntraCfg.Cmd.Ccall (Some lv, f, _, loc) ->
        let callees = Val.pow_proc_of_val (eval ~spec pid f mem loc n_info) in (* TODO: optimize this. memory access and du edges *)
        let retvar_set = PowProc.fold (fun f ->
          let ret = Loc.return_var f (Cil.typeOfLval lv) in
          PowLoc.add ret) callees PowLoc.empty in
        update Weak spec global (eval_lv ~spec pid lv mem loc ~n_info) (lookup retvar_set mem) mem
     | _ -> mem)
    |> (fun mem -> (mem, global))
  | IntraCfg.Cmd.Cskip -> (mem, global)
  | IntraCfg.Cmd.Casm _ -> (mem, global)    (* Not supported *)
  | _ -> invalid_arg "itvSem.ml: run_cmd"

let initial _ = Mem.bot
