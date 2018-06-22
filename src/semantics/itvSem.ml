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

module FP = Footprints
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
  if can_strong_update mode spec global locs then Mem.strong_update locs v mem
  else Mem.weak_update locs v mem

(* ********************************** *
 * Semantic functions for expressions *
 * ********************************** *)

let eval_const : Cil.constant -> Cil.location -> Val.t = fun cst loc ->
  let exp = CilHelper.s_exp (Const cst) in
  match cst with
  | Cil.CInt64 (i64, _, _) ->
    let itv = try Itv.of_int (Cil.i64_to_int i64) with _ -> Itv.top in
    Val.modify_footprints [%here] loc exp (Val.of_itv itv) 
  | Cil.CStr s -> Val.modify_footprints [%here] loc exp (Val.of_itv Itv.top)
  | Cil.CWStr s -> Val.modify_footprints [%here] loc exp (Val.of_itv Itv.top)
  | Cil.CChr c -> Val.modify_footprints [%here] loc exp (Val.of_itv (Itv.of_int (int_of_char c)))
  (* Float numbers are modified to itvs.  If you want to make a
     precise and sound analysis for float numbers, you have to
     develop a domain for them. *)
  | Cil.CReal (f, _, _) ->
   Val.modify_footprints [%here] loc exp (Val.of_itv (Itv.of_ints (int_of_float (floor f)) (int_of_float (ceil f))))
  (* Enum is not evaluated correctly in our analysis. *)
  | Cil.CEnum _ -> Val.modify_footprints [%here] loc exp (Val.of_itv Itv.top)

let eval_uop : Spec.t -> Cil.unop -> Val.t -> Cil.location -> string -> Val.t
= fun spec u v loc e ->
  if Val.eq v Val.bot then Val.bot else
    let fp = Val.footprints_of_val v in 
    let itv = Val.itv_of_val v in
    let itv', here =
      match u with
      | Cil.Neg -> Itv.minus (Itv.of_int 0) itv, [%here]
      | Cil.LNot -> Itv.l_not itv, [%here]
      | Cil.BNot -> if spec.Spec.unsound_bitwise then (Itv.bot, [%here]) else (Itv.unknown_unary itv, [%here])
    in
    Val.modify_footprints here loc e (Val.join (Val.of_footprints fp) (Val.of_itv itv'))

let eval_bop : Spec.t -> Cil.binop -> Val.t -> Val.t -> Cil.location -> string -> Val.t
  = fun spec b v1 v2 loc e ->
    let fp = Val.of_footprints (FP.join (Val.footprints_of_val v1) (Val.footprints_of_val v2)) in
    match b with
    | Cil.PlusA ->
      let v = Val.of_itv (Itv.plus (Val.itv_of_val v1) (Val.itv_of_val v2)) in
      Val.modify_footprints [%here] loc e (Val.join v fp)
    | Cil.PlusPI
    | Cil.IndexPI ->
      let ablk = Val.array_of_val v1 in
      let offset = Val.itv_of_val v2 in
      let ablk = ArrayBlk.plus_offset ablk offset in
      let v = Val.join (Val.of_pow_loc (Val.pow_loc_of_val v1)) (Val.of_array ablk) in
      Val.modify_footprints [%here] loc e (Val.join v fp)
  | Cil.MinusA ->
    let v = Val.of_itv (Itv.minus (Val.itv_of_val v1) (Val.itv_of_val v2)) in
    Val.modify_footprints [%here] loc e (Val.join v fp)
  | Cil.MinusPI ->
    let ablk = Val.array_of_val v1 in
    let offset = Val.itv_of_val v2 in
    let ablk = ArrayBlk.minus_offset ablk offset in
    let v = Val.join (Val.of_pow_loc (Val.pow_loc_of_val v1)) (Val.of_array ablk) in
    Val.modify_footprints [%here] loc e (Val.join v fp)
  | Cil.MinusPP ->
    let offset1 = Val.array_of_val v1 |> ArrayBlk.offsetof in
    let offset2 = Val.array_of_val v2 |> ArrayBlk.offsetof in
    let v = Itv.minus offset1 offset2 |> Val.of_itv in
    Val.modify_footprints [%here] loc e (Val.join v fp)
  | Cil.Mult ->
    let v = Val.of_itv (Itv.times (Val.itv_of_val v1) (Val.itv_of_val v2)) in
    Val.modify_footprints [%here] loc e (Val.join v fp)
  | Cil.Div ->
    let v = Val.of_itv (Itv.divide (Val.itv_of_val v1) (Val.itv_of_val v2)) in
    Val.modify_footprints [%here] loc e (Val.join v fp)
  | Cil.Lt ->
    let v = Val.of_itv (Itv.lt_itv (Val.itv_of_val v1) (Val.itv_of_val v2)) in
    Val.modify_footprints [%here] loc e (Val.join v fp)   
  | Cil.Gt ->
    let v = Val.of_itv (Itv.gt_itv (Val.itv_of_val v1) (Val.itv_of_val v2)) in
    Val.modify_footprints [%here] loc e (Val.join v fp) 
  | Cil.Le ->
    let v = Val.of_itv (Itv.le_itv (Val.itv_of_val v1) (Val.itv_of_val v2)) in
    Val.modify_footprints [%here] loc e (Val.join v fp) 
  | Cil.Ge ->
    let v = Val.of_itv (Itv.ge_itv (Val.itv_of_val v1) (Val.itv_of_val v2)) in
    Val.modify_footprints [%here] loc e (Val.join v fp) 
  | Cil.Eq ->
    let v = Val.of_itv (Itv.eq_itv (Val.itv_of_val v1) (Val.itv_of_val v2)) in
    Val.modify_footprints [%here] loc e (Val.join v fp) 
  | Cil.Ne ->
    let v = Val.of_itv (Itv.ne_itv (Val.itv_of_val v1) (Val.itv_of_val v2)) in
    Val.modify_footprints [%here] loc e (Val.join v fp) 
  | Cil.LAnd ->
    let v = Val.of_itv (Itv.l_and (Val.itv_of_val v1) (Val.itv_of_val v2)) in
    Val.modify_footprints [%here] loc e (Val.join v fp) 
  | Cil.LOr ->
    let v  = Val.of_itv (Itv.l_or (Val.itv_of_val v1) (Val.itv_of_val v2)) in
    Val.modify_footprints [%here] loc e (Val.join v fp) 
  | Cil.Shiftlt ->
    if spec.Spec.unsound_bitwise then Val.modify_footprints [%here] loc e v1
    else
      let v = Val.of_itv (Itv.l_shift (Val.itv_of_val v1) (Val.itv_of_val v2)) in
      Val.modify_footprints [%here] loc e (Val.join v fp)
  | Cil.Shiftrt | Cil.Mod | Cil.BAnd | Cil.BXor | Cil.BOr ->
    if spec.Spec.unsound_bitwise then Val.modify_footprints [%here] loc e v1
    else
      let v = Val.of_itv (Itv.unknown_binary (Val.itv_of_val v1) (Val.itv_of_val v2)) in
      Val.modify_footprints [%here] loc e (Val.join v fp)

let rec resolve_offset : Spec.t -> Proc.t -> Val.t -> Cil.offset -> Mem.t -> Footprints.t * Cil.location -> string -> PowLoc.t * Footprints.t
= fun spec pid v os mem (fp, loc) exp ->
  match os with
  | Cil.NoOffset ->
    let powloc, here =  PowLoc.join (Val.pow_loc_of_val v) (Val.array_of_val v |> ArrayBlk.pow_loc_of_array), [%here] in
    (powloc, FP.join fp (FP.of_here here loc exp))
  | Cil.Field (f, os') ->
    let (ploc, arr, str) = (Val.pow_loc_of_val v, Val.array_of_val v, Val.struct_of_val v) in
    let v =
      let v1 = StructBlk.append_field (Val.struct_of_val (lookup ploc mem)) f in (* Case1: S s; p = &s; p->f *)
      let v2 = ArrayBlk.append_field arr f in (* Case2:  p = (struct S* )malloc(sizeof(struct S)); p->f *)
      let v3 = StructBlk.append_field str f in (* Case3:  S s; s.f *)
      Val.of_pow_loc (PowLoc.join (PowLoc.join v1 v2) v3)
    in
    resolve_offset spec pid v os' mem (Footprints.join fp (FP.of_here [%here] loc exp), loc) exp
  | Cil.Index (e, os') ->
    let ploc = Val.pow_loc_of_val v in
    let arr = lookup ploc mem |> Val.array_of_val in
    let _ : ItvDom.Val.t = eval ~spec pid e mem loc in (* NOTE: to sync with access function *)
    let fp = Footprints.join fp (FP.of_here [%here] loc exp) in
    resolve_offset spec pid (ArrayBlk.pow_loc_of_array arr |> Val.of_pow_loc)  os' mem (fp, loc) exp

and eval_lv_with_footprint ?(spec=Spec.empty) : Proc.t -> Cil.lval -> Mem.t -> Cil.location -> PowLoc.t * Footprints.t
  = fun pid lv mem loc ->
    let exp = CilHelper.s_exp (Lval lv) in
    let v, here =
      match fst lv with
      | Cil.Var vi ->
        let l =  var_of_varinfo vi pid
                 |> PowLoc.singleton
                 |> Val.of_pow_loc in
        (l, [%here])
      | Cil.Mem e ->
        (eval ~spec pid e mem loc, [%here])
    in
    let powloc, fp = resolve_offset spec pid v (snd lv) mem (Footprints.of_here here loc exp, loc) exp in
    let powloc = PowLoc.remove Loc.null (powloc) in
    let fp = Footprints.join fp (Val.footprints_of_val v) in
    (powloc, fp)

and var_of_varinfo vi pid  =
  if vi.Cil.vglob then Loc.of_gvar vi.Cil.vname vi.Cil.vtype
  else Loc.of_lvar pid vi.Cil.vname vi.Cil.vtype

and eval ?(spec=Spec.empty) : Proc.t -> Cil.exp -> Mem.t -> Cil.location -> Val.t
  = fun pid e mem loc ->
    let s_exp = CilHelper.s_exp e in
    match e with
    | Cil.Const c -> Val.modify_footprints [%here] loc s_exp (eval_const c loc) 
    | Cil.Lval l -> 
      let powloc, fp = eval_lv_with_footprint ~spec pid l mem loc in
      let v = lookup powloc mem in
      Val.modify_footprints' [%here] fp loc s_exp v
    | Cil.SizeOf t ->
      let sizeOf, here =
        Val.of_itv (try CilHelper.byteSizeOf t |> Itv.of_int with _ -> Itv.pos), [%here] in
      Val.modify_footprints here loc s_exp sizeOf
    | Cil.SizeOfE e ->
      let sizeOfE, here =
        Val.of_itv (try CilHelper.byteSizeOf (Cil.typeOf e) |> Itv.of_int with _ -> Itv.pos), [%here] in
      Val.modify_footprints here loc s_exp sizeOfE
    | Cil.SizeOfStr s ->
      let sizeOfStr, here = Val.of_itv (Itv.of_int (String.length s + 1)), [%here] in
    Val.modify_footprints here loc s_exp sizeOfStr
    | Cil.AlignOf t ->
    let alignOf, here = Val.of_itv (Itv.of_int (Cil.alignOf_int t)), [%here] in
    Val.modify_footprints here loc s_exp alignOf
  (* TODO: type information is required for precise semantics of AlignOfE.  *)
  | Cil.AlignOfE _ -> Val.modify_footprints [%here] loc s_exp (Val.of_itv Itv.top)
  | Cil.UnOp (u, e, _) ->
    let v, here= (eval_uop spec u (eval ~spec pid e mem loc) loc s_exp), [%here] in
    Val.modify_footprints here loc s_exp v
  | Cil.BinOp (b, e1, e2, _) ->
    let v1 = eval ~spec pid e1 mem loc in
    let v2 = eval ~spec pid e2 mem loc in
    Val.modify_footprints [%here] loc s_exp (eval_bop spec b v1 v2 loc s_exp) 
  | Cil.Question (e1, e2, e3, _) ->
    let i1 = Val.itv_of_val (eval ~spec pid e1 mem loc) in
    if Itv.is_bot i1 then
      Val.modify_footprints [%here] loc s_exp Val.bot
    else if Itv.eq (Itv.of_int 0) i1 then
      Val.modify_footprints [%here] loc s_exp (eval ~spec pid e3 mem loc)
    else if not (Itv.le (Itv.of_int 0) i1) then
      Val.modify_footprints [%here] loc s_exp (eval ~spec pid e2 mem loc)
    else
      let v, here = Val.join (eval ~spec pid e2 mem loc) (eval ~spec pid e3 mem loc), [%here] in
      Val.modify_footprints here loc s_exp v
  | Cil.CastE (t, e) ->
    let v, here = eval ~spec pid e mem loc, [%here] in
    (try Val.modify_footprints [%here] loc s_exp (Val.cast (Cil.typeOf e) t v)
     with _ -> Val.modify_footprints here loc s_exp v)
  | Cil.AddrOf l ->
    let powloc, fp = eval_lv_with_footprint ~spec pid l mem loc in
    Val.modify_footprints' [%here] fp loc s_exp (Val.of_pow_loc powloc)
  | Cil.AddrOfLabel _ ->
    invalid_arg "itvSem.ml:eval AddrOfLabel mem. \
                 Analysis does not support label values."
  | Cil.StartOf l ->
    let powloc, fp = eval_lv_with_footprint ~spec pid l mem loc in
    Val.modify_footprints' [%here] fp loc s_exp (lookup powloc mem)

let eval_lv ?(spec=Spec.empty) pid lv mem loc = fst (eval_lv_with_footprint ~spec pid lv mem loc)

let eval_list : Spec.t -> Proc.t -> Cil.exp list -> Mem.t -> Cil.location -> Val.t list
= fun spec pid exps mem loc ->
  List.map (fun e -> Val.modify_footprints [%here] loc (CilHelper.s_exp e) (eval ~spec pid e mem loc)) exps

let eval_array_alloc ?(spec=Spec.empty) : Node.t -> Cil.exp -> bool -> Mem.t -> Cil.location -> Val.t
= fun node e is_static mem loc ->
  let pid = Node.get_pid node in
  let allocsite = Allocsite.allocsite_of_node node in
  let o = Itv.of_int 0 in
  let sz = Val.itv_of_val (eval ~spec pid e mem loc) in
  (* NOTE: stride is always one when allocating memory. *)
  let st = Itv.of_int 1 in
  let np = Itv.nat in
  let pow_loc = if is_static then PowLoc.bot else PowLoc.singleton Loc.null in
  let array, here = ArrayBlk.make allocsite o sz st np, [%here] in
  Val.modify_footprints here loc (CilHelper.s_exp e) (Val.join (Val.of_pow_loc pow_loc) (Val.of_array array))

let eval_struct_alloc : PowLoc.t -> Cil.compinfo -> Cil.location -> string -> Val.t
  = fun lv comp loc exp ->
    StructBlk.make lv comp |> Val.of_struct |> Val.modify_footprints [%here] loc exp

let eval_string_alloc : Node.t -> string -> Mem.t -> Cil.location -> Val.t
  = fun node s mem loc ->
    let s_exp =  CilHelper.s_exp (Cil.Const (Cil.CStr s)) in
    let allocsite = Allocsite.allocsite_of_string node in
    let o = Itv.of_int 0 in
    let sz = Itv.of_int (String.length s + 1) in
    let st = Itv.of_int 1 in
    let np = Itv.of_int (String.length s) in
    let array = ArrayBlk.make allocsite o sz st np in
    Val.of_array array |> Val.modify_footprints [%here] loc s_exp


let eval_string : string -> Val.t = fun s ->
  Val.of_itv Itv.nat

(* ****************************** *
 * Semantic functions for pruning *
 * ****************************** *)

let rec prune_simple : update_mode -> Spec.t -> Global.t -> Proc.t -> exp -> Mem.t -> Cil.location
  -> Mem.t
= fun mode spec global pid cond mem loc->
  match cond with
  | BinOp (op, Lval x, e, t)
    when op = Lt || op = Gt || op = Le || op = Ge || op = Eq || op = Ne ->
    let x_lv = eval_lv ~spec pid x mem loc in
    if PowLoc.cardinal x_lv = 1 then
      let x_v = lookup x_lv mem in
      let e_v = eval ~spec pid e mem loc |> Val.itv_of_val in
      let x_itv = Val.itv_of_val x_v in
      let x_ploc = Val.pow_loc_of_val x_v in
      let x_itv = Itv.prune op x_itv e_v in
      let x_ploc = PowLoc.prune op x_ploc e in
      let x_pruned = Val.make (x_itv, x_ploc, Val.array_of_val x_v, Val.struct_of_val x_v,
                               Val.pow_proc_of_val x_v, Val.footprints_of_val x_v) in
      update mode spec global x_lv x_pruned mem
    else mem
  | BinOp (op, e1, e2, _) when op = LAnd || op = LOr ->
    let mem1 = prune_simple mode spec global pid e1 mem loc in
    let mem2 = prune_simple mode spec global pid e2 mem loc in
    if op = LAnd then Mem.meet mem1 mem2 else Mem.join mem1 mem2
  | UnOp (LNot, Lval x, _) ->
    let x_lv = eval_lv ~spec pid x mem loc in
    if PowLoc.cardinal x_lv = 1 then
      let x_v = lookup x_lv mem in
      let x_itv = Val.itv_of_val x_v in
      let e_v = Itv.zero in
      let x_itv = Itv.meet x_itv e_v in
      let x_pruned = Val.modify_itv x_itv x_v in
      update mode spec global x_lv x_pruned mem
    else mem
  | Lval x ->
    let x_lv = eval_lv ~spec pid x mem loc in
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

let prune : update_mode -> Spec.t -> Global.t -> Proc.t -> exp -> Mem.t -> Cil.location -> Mem.t
= fun mode spec global pid cond mem loc ->
  match CilHelper.make_cond_simple cond with
  | None -> mem
  | Some cond_simple -> prune_simple mode spec global pid cond_simple mem loc

(* ******************************* *
 * Semantic functions for commands *
 * ******************************* *)
let sparrow_print spec pid exps mem loc =
  if !Options.verbose < 1 then ()
  else
    let vs = eval_list spec pid exps mem loc in
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

let model_alloc_one mode spec pid lvo f (mem, global) loc =
  match lvo with
    None -> (mem, global)
  | Some lv ->
    let allocsite = Allocsite.allocsite_of_ext (Some f.vname) in
    let arr_val = ItvDom.Val.of_array (ArrayBlk.make allocsite Itv.zero Itv.one Itv.one Itv.nat) in
    let ext_loc = PowLoc.singleton (Loc.of_allocsite allocsite) in
    let mem = update mode spec global (eval_lv ~spec pid lv mem loc) arr_val mem in
    let mem = update mode spec global ext_loc Val.itv_top mem in
    (mem,global)

let model_realloc mode spec node (lvo, exps) (mem, global) loc =
  let pid = Node.get_pid node in
  match lvo with
  | Some lv ->
    begin
      match exps with
      | _::size::_ ->
        (update mode spec global (eval_lv ~spec pid lv mem loc) (eval_array_alloc ~spec node size false mem loc) mem, global)
      | _ -> raise (Failure "Error: arguments of realloc are not given")
    end
  | _ -> (mem,global)

let model_calloc mode spec node (lvo, exps) (mem, global) loc =
  let pid = Node.get_pid node in
  match lvo with
  | Some lv ->
    begin
      match exps with
      | n::size::_ ->
        let new_size = Cil.BinOp (Cil.Mult, n, size, Cil.uintType) in
        (update mode spec global (eval_lv ~spec pid lv mem loc) (eval_array_alloc ~spec node new_size false mem loc) mem, global)
      | _ -> raise (Failure "Error: arguments of realloc are not given")
    end
  | _ -> (mem,global)

let model_scanf mode spec pid exps (mem, global) loc =
  match exps with
    _::t ->
      List.fold_left (fun (mem, global) e ->
          match e with
              Cil.AddrOf lv ->
              let mem = update mode spec global (eval_lv ~spec pid lv mem loc) Val.itv_top mem in
              (mem, global)
          | _ -> (mem,global)) (mem,global) t
  | _ -> (mem, global)

let model_strdup mode spec node (lvo, exps) (mem, global) loc' =
  let pid = Node.get_pid node in
  match (lvo, exps) with
  | (Some lv, str::_) ->
    let allocsite = Allocsite.allocsite_of_node node in
    let str_val = eval ~spec pid str mem loc'|> ItvDom.Val.array_of_val in
    let size = ArrayBlk.sizeof str_val in
    let null_pos = ArrayBlk.nullof str_val in
    let allocsites = ArrayBlk.pow_loc_of_array str_val in
    let offset = Itv.zero in
    let arr_val = ArrayBlk.make allocsite Itv.zero (Itv.minus size offset) Itv.one null_pos in
    let loc = PowLoc.singleton (Loc.of_allocsite allocsite) in
    let v = Val.join (Val.of_array arr_val) (Val.of_pow_loc loc) in
    let mem = update mode spec global (eval_lv ~spec pid lv mem loc') v mem in
    let mem = update mode spec global loc (lookup allocsites mem) mem in
    (mem,global)
  | _ -> (mem,global)

let model_input mode spec pid lvo (mem, global) loc = 
  match lvo with
    Some lv ->
      let allocsite = Allocsite.allocsite_of_ext None in
      let ext_v = Val.external_value allocsite in
      let ext_loc = PowLoc.singleton (Loc.of_allocsite allocsite) in
      let mem = update mode spec global (eval_lv ~spec pid lv mem loc) ext_v mem in
      let mem = update mode spec global ext_loc Val.itv_top mem in
        (mem,global)
  | _ -> (mem,global)

let model_assign mode spec pid (lvo,exps) (mem, global) loc =
  match (lvo,exps) with
    (Some lv, e::_) ->
    (update mode spec global (eval_lv ~spec pid lv mem loc) (eval ~spec pid e mem loc) mem, global)
  | (_, _) -> (mem,global)


let model_strlen mode spec pid (lvo, exps) (mem, global) loc =
  match (lvo, exps) with
  | (Some lv, str::_) ->
    let str_val = eval ~spec pid str mem loc in
    let null_pos = ArrayBlk.nullof (ItvDom.Val.array_of_val str_val) in
    let itv, here = (Itv.meet Itv.nat null_pos), [%here] in
    let s_exp = "strlen("^CilHelper.s_exp str^")" in
    let v = Val.modify_footprints' here (Val.footprints_of_val str_val) loc s_exp (Val.of_itv itv) in
    let lv = eval_lv ~spec pid lv mem loc in
    (update mode spec global lv v mem, global)
  | _ -> (mem,global)

let rec model_fgets mode spec pid (lvo, exps) (mem, global) loc = 
  match (lvo, exps) with
  | (_, Lval buf::size::_) | (_, StartOf buf::size::_) ->
    let size_itv = eval ~spec pid size mem loc |> ItvDom.Val.itv_of_val in
    let buf_lv = eval_lv ~spec pid buf mem loc in
    let buf_arr = lookup buf_lv mem |> ItvDom.Val.array_of_val in
    let allocsites = ArrayBlk.pow_loc_of_array buf_arr in
    let buf_val = ArrayBlk.set_null_pos buf_arr (Itv.join Itv.zero size_itv) |> ItvDom.Val.of_array in
    mem
    |> update mode spec global buf_lv buf_val
    |> update mode spec global allocsites Val.itv_top
    |> (fun mem -> (mem, global))
  | (_, CastE (_, buf)::size::e) -> model_fgets mode spec pid (lvo, buf::size::e) (mem, global) loc
  | _ -> (mem,global)

let rec model_sprintf mode spec pid (lvo, exps) (mem, global) loc =
  let s_exp = "sprintf("^(CilHelper.s_exp (List.hd exps))^","^CilHelper.s_exp (List.nth exps 1)^",...)"in
  match exps with
  | Lval buf::str::[] | StartOf buf::str::[] ->  (* format string *)
    let str_val = eval ~spec pid str mem loc |> ItvDom.Val.array_of_val in
    let (arrays, null_pos) = (ArrayBlk.pow_loc_of_array str_val, ArrayBlk.nullof str_val) in
    let buf_lv = eval_lv ~spec pid buf mem loc in
    let buf_arr = lookup buf_lv mem |> ItvDom.Val.array_of_val in
    let allocsites = ArrayBlk.pow_loc_of_array buf_arr in
    let buf_val, here = (ArrayBlk.set_null_pos buf_arr null_pos |> ItvDom.Val.of_array), [%here] in
    let buf_val = Val.modify_footprints here loc s_exp buf_val in
    mem
    |> update mode spec global buf_lv buf_val
    |> update mode spec global allocsites (lookup arrays mem)
    |> (match lvo with 
        | Some lv ->
          let v = Val.modify_footprints [%here] loc s_exp (Val.of_itv null_pos) in
          update mode spec global (eval_lv ~spec pid lv mem loc) v
        | _ -> id)
    |> (fun mem -> (mem, global))
  | CastE (_, buf)::str::[]
  | buf::CastE (_, str)::[] -> model_sprintf mode spec pid (lvo, buf::str::[]) (mem, global) loc
  | _ ->
    begin
      match lvo with
        Some lv ->
        let v = Val.modify_footprints [%here] loc s_exp (Val.of_itv Itv.nat) in
        (update mode spec global (eval_lv ~spec pid lv mem loc) v mem, global)
      | _ -> (mem,global)
    end

(* argc, argv *)
let sparrow_arg mode spec pid exps (mem,global) loc =
  match exps with
    (Cil.Lval argc)::(Cil.Lval argv)::_ ->
      let argv_a = Allocsite.allocsite_of_ext (Some "argv") in
      let argv_v = Val.of_array (ArrayBlk.input argv_a) in
      let arg_a = Allocsite.allocsite_of_ext (Some "arg") in
      let arg_v = Val.of_array (ArrayBlk.input arg_a) in
      (update mode spec global (eval_lv ~spec pid argc mem loc) (Val.of_itv Itv.pos) mem
      |> update mode spec global (eval_lv ~spec pid argv mem loc) argv_v
      |> update mode spec global (PowLoc.singleton (Loc.of_allocsite argv_a)) arg_v
      |> update mode spec global (PowLoc.singleton (Loc.of_allocsite arg_a)) (Val.of_itv Itv.top), global)
  | _ -> (mem,global)

(* optind, optarg *)
let sparrow_opt mode spec pid exps (mem,global) loc =
  match exps with
    (Cil.Lval optind)::(Cil.Lval optarg)::_ ->
      let arg_a = Allocsite.allocsite_of_ext (Some "arg") in
      let arg_v = Val.of_array (ArrayBlk.input arg_a) in
      (update mode spec global (eval_lv ~spec pid optind mem loc) (Val.of_itv Itv.nat) mem
      |> update mode spec global (eval_lv ~spec pid optarg mem loc) arg_v
      |> update mode spec global (PowLoc.singleton (Loc.of_allocsite arg_a)) (Val.of_itv Itv.top), global)
  | _ -> (mem,global)

let model_unknown mode spec node pid lvo f exps (mem, global) loc =
  match lvo with
    None -> (mem, global)
  | Some lv when Cil.isArithmeticType (Cil.unrollTypeDeep (Cil.typeOfLval lv)) ->
      let ext_v = if CilHelper.is_unsigned (Cil.unrollTypeDeep (Cil.typeOfLval lv)) then
                    Val.of_itv Itv.nat
                  else Val.of_itv Itv.top
      in
      let lv = eval_lv ~spec pid lv mem loc in
      let mem = update mode spec global lv ext_v mem in
      (mem,global)
  | Some lv ->
      let allocsite = Allocsite.allocsite_of_ext (Some f.vname) in
      let ext_v = ArrayBlk.extern allocsite |> ArrayBlk.cast_array (Cil.typeOfLval lv) |> Val.of_array in
      let ext_loc = PowLoc.singleton (Loc.of_allocsite allocsite) in
      let lv = eval_lv ~spec pid lv mem loc in
      let mem = update mode spec global lv ext_v mem in
      let mem = update mode spec global ext_loc Val.itv_top mem in
      (mem,global)

let model_memcpy mode spec pid (lvo, exps) (mem, global) loc =
  match (lvo, exps) with
    Some lv, dst::src::_ ->
      let (src_v, dst_v) = tuple mem |> Tuple2.map (fun mem -> eval ~spec pid src mem loc) (fun mem -> eval ~spec pid dst mem loc) in
      let (src_l, dst_l) = (src_v, dst_v) |> Tuple2.mapn Val.array_of_val
                           |> Tuple2.mapn ArrayBlk.pow_loc_of_array in
      let lv = eval_lv ~spec pid lv mem loc in
      mem
      |> update mode spec global dst_l (lookup src_l mem)
      |> update mode spec global lv dst_v
      |> (fun mem -> (mem, global))
  | _, _ -> (mem, global)

let model_getpwent mode spec node pid lvo f (mem,global) loc =
  match lvo, f.vtype with
    Some lv, Cil.TFun ((Cil.TPtr ((Cil.TComp (comp, _) as elem_t), _) as ptr_t), _, _, _) ->
      let struct_loc = eval_lv ~spec pid lv mem loc in
      let struct_v = eval_array_alloc ~spec node (Cil.SizeOf elem_t) false mem loc |> Val.cast ptr_t (Cil.typeOfLval lv) in
      let field_loc = ArrayBlk.append_field (Val.array_of_val struct_v) (List.find (fun f -> f.fname ="pw_name") comp.cfields) in
      let allocsite = Allocsite.allocsite_of_ext (Some "getpwent.pw_name") in
      let ext_v = ArrayBlk.input allocsite |> Val.of_array in
      let ext_loc = PowLoc.singleton (Loc.of_allocsite allocsite) in
      let mem = update mode spec global struct_loc struct_v mem
              |> update mode spec global field_loc ext_v
              |> update mode spec global ext_loc Val.itv_top in
      (mem, global)
  | _ -> (mem, global)

let rec model_strcpy mode spec node pid es (mem, global) loc =
  match es with
    (CastE (_, e))::t -> model_strcpy mode spec node pid (e::t) (mem,global) loc
  | dst::(CastE(_, e))::[] -> model_strcpy mode spec node pid (dst::e::[]) (mem,global) loc
  | (Lval dst)::(Lval src)::[] | (StartOf dst)::(StartOf src)::[]
  | (Lval dst)::(StartOf src)::[] | (StartOf dst)::(Lval src)::[] ->
      let src_arr = Val.array_of_val (lookup (eval_lv ~spec pid src mem loc) mem) in
      let dst_arr = Val.array_of_val (lookup (eval_lv ~spec pid dst mem loc) mem) in
      let np = ArrayBlk.nullof src_arr in
      let newv = Val.of_array (ArrayBlk.set_null_pos dst_arr np) in
      let mem = mem |> update mode spec global (eval_lv ~spec pid dst mem loc) newv in
      (mem, global)
  | _ -> (mem, global)

let rec model_strncpy mode spec node pid es (mem, global) loc =
  match es with
    CastE (_, e)::t -> model_strncpy mode spec node pid (e::t) (mem, global) loc
  | (Lval dst)::_::size::_
  | (StartOf dst)::_::size::_ ->
      let arr = Val.array_of_val (lookup (eval_lv ~spec pid dst mem loc) mem) in
      let sz = Val.itv_of_val (eval ~spec pid size mem loc) in
      let np = Itv.join Itv.zero (Itv.minus sz Itv.one)in
      let newv = Val.of_array (ArrayBlk.set_null_pos arr np) in
      let mem = mem |> update mode spec global (eval_lv ~spec pid dst mem loc) newv in
      (mem, global)
  | _ -> (mem,global)

let rec model_strcat mode spec node pid es (mem, global) loc =
  match es with
    (CastE (_, e))::t -> model_strcat mode spec node pid (e::t) (mem,global) loc
  | dst::(CastE(_, e))::[] -> model_strcat mode spec node pid (dst::e::[]) (mem,global) loc
  | (Lval dst)::(Lval src)::[] | (StartOf dst)::(StartOf src)::[]
  | (Lval dst)::(StartOf src)::[] | (StartOf dst)::(Lval src)::[] ->
      let src_arr = Val.array_of_val (lookup (eval_lv ~spec pid src mem loc) mem) in
      let dst_arr = Val.array_of_val (lookup (eval_lv ~spec pid dst mem loc) mem) in
      let np = ArrayBlk.nullof src_arr in
      let newv = Val.of_array (ArrayBlk.plus_null_pos dst_arr np) in
      let mem = mem |> update mode spec global (eval_lv ~spec pid dst mem loc) newv in
      (mem, global)
  | _ -> (mem, global)

let rec model_strchr mode spec node pid (lvo, exps) (mem, global) loc =
  match lvo, exps with
    Some _, (CastE (_, e))::t -> model_strchr mode spec node pid (lvo, e::t) (mem,global) loc
  | Some lv, (Lval str)::_ | Some lv, (StartOf str)::_ ->
      let str_arr = Val.array_of_val (lookup (eval_lv ~spec pid str mem loc) mem) in
      let np = ArrayBlk.nullof str_arr in
      let newv = Val.of_array (ArrayBlk.plus_offset str_arr np) in
      let mem = mem |> update mode spec global (eval_lv ~spec pid lv mem loc) newv in
      (mem, global)
  | _, _ -> (mem, global)

let sparrow_array_init mode spec node pid exps (mem, global) loc lvo =
  match List.nth exps 0, List.nth exps 1 with
  | arr, Cil.Const (Cil.CInt64 (_, _, _)) ->
      let lv = eval ~spec pid arr mem loc |> Val.array_of_val |> ArrayBlk.pow_loc_of_array in
      let v = List.fold_left (fun v e -> Val.join (eval ~spec pid e mem loc) v) Val.bot (List.tl exps) in
      (update mode spec global lv v mem, global)
  | arr, Cil.Const (Cil.CStr s) ->
      let lv = eval ~spec pid arr mem loc |> Val.array_of_val |> ArrayBlk.pow_loc_of_array in
      let v = List.fold_left (fun v e ->
          match e with
            Cil.Const (Cil.CStr s) ->
              Val.join (eval_string_alloc node s mem loc) v
          | _ -> v) Val.bot (List.tl exps)
      in
      (update mode spec global lv v mem, global)
  | arr, _ ->
    let getLval e =
      match e with
      | Cil.Lval l -> eval_lv ~spec pid l mem loc
      | _ -> raise (Failure "Error: not Lval ")
    in
    let s_exp = "sp_arr_init("^CilHelper.s_exp arr^")" in
    let v = Val.modify_footprints [%here] loc s_exp (eval ~spec pid arr mem loc) in
    (update mode spec global (getLval arr) v mem, global)

let mem_alloc_libs = ["__ctype_b_loc"; "initscr"; "newwin"; "localtime"; "__errno_location"; "opendir"; "readdir"]
let scaffolded_functions mode spec node pid (lvo,f,exps) (mem, global) loc =
  if !Options.scaffold then
    match f.vname with
    | "fgets" -> model_fgets mode spec pid (lvo, exps) (mem, global) loc
    | "sprintf" -> model_sprintf mode spec pid (lvo, exps) (mem, global) loc
    | "scanf" -> model_scanf mode spec pid exps (mem, global) loc
    | "getenv" -> model_input mode spec pid lvo (mem, global) loc
    | "strdup" -> model_strdup mode spec node (lvo, exps) (mem, global) loc
    | "gettext" -> model_assign mode spec pid (lvo, exps) (mem, global) loc
    | "memcpy" -> model_memcpy mode spec pid (lvo, exps) (mem, global) loc
    | "getpwent" -> model_getpwent mode spec node pid lvo f (mem,global) loc
    | "strcpy" -> model_strcpy mode spec node pid exps (mem, global) loc
    | "strncpy" -> model_strncpy mode spec node pid exps (mem, global) loc
    | "strcat" -> model_strcat mode spec node pid exps (mem, global) loc
    | "strchr" | "strrchr" -> model_strchr mode spec node pid (lvo, exps) (mem, global) loc
    | s when List.mem s mem_alloc_libs -> model_alloc_one mode spec pid lvo f (mem, global) loc
    | _ -> model_unknown mode spec node pid lvo f exps (mem, global) loc
  else
    model_unknown mode spec node pid lvo f exps (mem, global) loc

let handle_undefined_functions mode spec node pid (lvo,f,exps) (mem,global) loc =
  match f.vname with
  | "sparrow_arg" -> sparrow_arg mode spec pid exps (mem,global) loc
  | "sparrow_opt" -> sparrow_opt mode spec pid exps (mem,global) loc
  | "sparrow_print" -> sparrow_print spec pid exps mem loc; (mem,global)
  | "sparrow_dump" -> sparrow_dump mem loc; (mem,global)
  | "sparrow_assume" -> (prune mode spec global pid (List.hd exps) mem loc, global)
  | "sparrow_array_init" -> sparrow_array_init mode spec node pid exps (mem, global) loc lvo
  | "strlen" -> model_strlen mode spec pid (lvo, exps) (mem, global) loc
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
  match InterCfg.cmdof global.icfg node with
  | IntraCfg.Cmd.Cset (l, e, loc) ->
      (update mode spec global (eval_lv ~spec pid l mem loc) (eval ~spec pid e mem loc) mem, global)
  | IntraCfg.Cmd.Cexternal (l, loc) ->
    (match Cil.typeOfLval l with
       Cil.TInt (_, _) | Cil.TFloat (_, _) ->
         let ext_v = Val.of_itv Itv.top in
         let mem = update mode spec global (eval_lv ~spec pid l mem loc) ext_v mem in
         (mem,global)
     | _ ->
       let allocsite = Allocsite.allocsite_of_ext None in
       let ext_v = Val.external_value allocsite in
       let ext_loc = PowLoc.singleton (Loc.of_allocsite allocsite) in
       let mem = update mode spec global (eval_lv ~spec pid l mem loc) ext_v mem in
       let mem = update mode spec global ext_loc ext_v mem in
        (mem,global))
  | IntraCfg.Cmd.Calloc (l, IntraCfg.Cmd.Array e, is_static, loc) ->
    (update mode spec global (eval_lv ~spec pid l mem loc) (eval_array_alloc ~spec node e is_static mem loc) mem, global)
  | IntraCfg.Cmd.Calloc (l, IntraCfg.Cmd.Struct s, is_static, loc) ->
    let lv = eval_lv ~spec pid l mem loc in
    (update mode spec global lv (eval_struct_alloc lv s loc (CilHelper.s_exp (Lval l))) mem, global)
  | IntraCfg.Cmd.Csalloc (l, s, loc) ->
    let str_loc =
      Allocsite.allocsite_of_string node
      |> Loc.of_allocsite |> PowLoc.singleton
    in
    mem
    |> update mode spec global (eval_lv ~spec pid l mem loc) (eval_string_alloc node s mem loc)
    |> update mode spec global str_loc (eval_string s)
    |> (fun mem -> (mem, global))
  | IntraCfg.Cmd.Cfalloc (l, fd, loc) ->
    let clos = Val.of_pow_proc (PowProc.singleton fd.svar.vname) in
    (update mode spec global (eval_lv ~spec pid l mem loc) clos mem, global)
  | IntraCfg.Cmd.Cassume (e, loc) ->
    let _ : ItvDom.Val.t = eval ~spec pid e mem loc in (* for inspection *)
    (prune mode spec global pid e mem loc, global)
  | IntraCfg.Cmd.Ccall (lvo, Cil.Lval (Cil.Var f, Cil.NoOffset), arg_exps, loc)
    when Global.is_undef f.vname global -> (* undefined library functions *)
    if BatSet.mem ((CilHelper.s_location loc)^":"^f.vname) spec.Spec.unsound_lib then (mem,global)
    else
      let _ : ItvDom.Val.t list = eval_list spec pid arg_exps mem loc in (* for inspection *)
      handle_undefined_functions mode spec node pid (lvo,f,arg_exps) (mem,global) loc
  | IntraCfg.Cmd.Ccall (lvo, f, arg_exps, loc) -> (* user functions *)
    let fs = Val.pow_proc_of_val (eval ~spec pid f mem loc) in
    if PowProc.eq fs PowProc.bot then (mem, global)
    else
      let arg_lvars_of_proc f acc =
        let args = InterCfg.argsof global.icfg f in
        let lvars = List.map (fun x -> Loc.of_lvar f x.Cil.vname x.Cil.vtype) args in
        BatSet.add lvars acc in
      let arg_lvars_set = PowProc.fold arg_lvars_of_proc fs BatSet.empty in
      let arg_vals = eval_list spec pid arg_exps mem loc in
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
              Dump.weak_add f (eval_lv ~spec pid lv mem loc) d
           ) fs global.dump in
      let mem = bind_arg_lvars_set mode spec global arg_lvars_set arg_vals mem in
      (mem, { global with dump })
  | IntraCfg.Cmd.Creturn (ret_opt, loc) ->
      (match ret_opt with
      | None -> mem
      | Some e ->
        update Weak spec global (Loc.return_var pid (Cil.typeOf e) |> PowLoc.singleton) (eval ~spec pid e mem loc) mem)
      |> (fun mem -> (mem, global))
  | IntraCfg.Cmd.Cskip when InterCfg.is_returnnode node global.icfg ->
    let callnode = InterCfg.callof node global.icfg in
    (match InterCfg.cmdof global.icfg callnode with
       IntraCfg.Cmd.Ccall (Some lv, f, _, loc) ->
        let callees = Val.pow_proc_of_val (eval ~spec pid f mem loc) in (* TODO: optimize this. memory access and du edges *)
        let retvar_set = PowProc.fold (fun f ->
          let ret = Loc.return_var f (Cil.typeOfLval lv) in
          PowLoc.add ret) callees PowLoc.empty in
        update Weak spec global (eval_lv ~spec pid lv mem loc) (lookup retvar_set mem) mem
     | _ -> mem)
    |> (fun mem -> (mem, global))
  | IntraCfg.Cmd.Cskip -> (mem, global)
  | IntraCfg.Cmd.Casm _ -> (mem, global)    (* Not supported *)
  | _ -> invalid_arg "itvSem.ml: run_cmd"
           
let initial _ = Mem.bot
