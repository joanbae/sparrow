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
open AbsDom
open ProdDom
open BasicDom
open Vocab

module Struct =
struct
  include String
  let to_string = id
  let pp fmt x = Format.fprintf fmt "%s" x
end

module PowStruct = struct
  include PowDom.MakeCPO (Struct)
  let priority x = if cardinal x >=2 then 3 else 0
  let pp fmt x =
    let rec pp_elt fmt x =
      if cardinal x = 1 then Format.fprintf fmt "@[<h>%a@]" Struct.pp (choose x)
      else iter (fun elt -> Format.fprintf fmt "@[<h>%a,@]" Struct.pp elt) x
    in
    if is_empty x then Format.fprintf fmt "bot"
    else Format.fprintf fmt "@[<hov 2>{%a}@]" pp_elt x
end

include MapDom.MakeLAT (Loc) (PowStruct)

let make : PowLoc.t -> Cil.compinfo -> t
= fun ploc s ->
  PowLoc.fold (fun l ->
    add l (PowStruct.singleton s.Cil.cname)) ploc bot

let append_field : t -> Cil.fieldinfo -> PowLoc.t
= fun s f ->
  foldi (fun loc info ->
      if PowStruct.mem f.Cil.fcomp.Cil.cname info then
        PowLoc.add (Loc.append_field loc f.Cil.fname f.Cil.ftype)
      else id) s PowLoc.bot

let pow_loc_of_struct : t -> PowLoc.t = fun str ->
  foldi (fun k _ -> PowLoc.add k) str PowLoc.bot

let extern () =
  if !Options.top_location then top
  else bot

let to_string : t -> string = fun x ->
  if is_empty x then "\"bot\"" else
  foldi (fun a b s ->
      let str = "{"^A.to_string a ^ ", \"structinfo\": \"" ^ B.to_string b ^"\"}" in
      link_by_sep "\n\t" str s) x ""

let priority ?(isPointer=false) x =
  (* We assume there is only one element in the map *)
  (* Further inspection is needed *)
  (* ex) (main,data1) -> {_CALC_DATA___1} *)
  try PowStruct.priority (snd (choose x)) with Not_found -> 0


let pp fmt m =
  if is_empty m then Format.fprintf fmt "\"Structsite\":\"bot\", \"structinfo\":\"bot\""
  else
   let k =  foldi (fun a b s ->
        let str = A.to_string a ^ ",\"structinfo\": \"" ^ B.to_string b ^"\"" in
        link_by_sep "\n\t" str s) m "" in
    Format.fprintf fmt "@[<hov 2>\"Structsite\":{ %s }@]" k
