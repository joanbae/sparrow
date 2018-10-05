open Vocab
open ItvDom

module DM = Debugmode
module Table = ItvDom.Table
let max_count = ref 0

let remove_extra_fps fp =
  Footprints.filter (fun fp -> fp.order < !max_count) fp

let remove_extra_fps' v =
  let v_only = Val.without_fp v in
  Val.modify_fp_only v_only (remove_extra_fps (Val.footprints_of_val v))

let add_lv pid lv mem loc n_num =
  let (powloc, lv_fp, fp_opt) = ItvSem.eval_lv_with_footprint pid lv mem loc n_num in
  let v = ItvDom.Mem.lookup powloc mem in
  DM.long (fun () ->
      if v = Val.bot then
        let () = Format.fprintf Format.err_formatter "%s" "Value is bot and its ploc was computed in the following way" in
        Format.fprintf Format.err_formatter "@\n=======@\n";
        Footprints.pp Format.err_formatter (Footprints.singleton lv_fp)
      else
      (* BasicDom.PowLoc.pp Format.err_formatter powloc;
       * Format.fprintf Format.err_formatter "@\n=======@\n";
       * Footprints.pp Format.err_formatter fp *)
        ItvDom.Val.pp Format.err_formatter v;)

let add_exp pid e mem loc n_num =
  let v = remove_extra_fps' (ItvSem.eval pid e mem loc n_num) in
  DM.long (fun () -> ItvDom.Val.pp Format.err_formatter v)

let add_exps i q =
  let node = q.Report.node in
  let pid = InterCfg.Node.get_pid node in
  (* let n_num = IntraCfg.Node.id (InterCfg.Node.get_cfgnode node) in *)
  let n_num = InterCfg.Node.to_string node in
  let mem = Table.find node i in
  match q.Report.exp with
  | ArrayExp (lv, e, loc) ->
    DM.empty
    |> DM.add (CilHelper.s_lv lv) (fun _ -> add_lv pid lv mem loc n_num)
    |> DM.add (CilHelper.s_exp e) (fun _ -> add_exp pid e mem loc n_num)
    |> DM.final
  | DerefExp (e, loc) ->
    DM.empty
    |> DM.add (CilHelper.s_exp e) (fun _ -> add_exp pid e mem loc n_num)
    |> DM.final
  | DivExp (e1, e2, loc)
  | Strcpy (e1, e2, loc)
  | Strcat (e1, e2, loc) ->
    DM.empty
    |> DM.add (CilHelper.s_exp e1) (fun _ -> add_exp pid e1 mem loc n_num)
    |> DM.add (CilHelper.s_exp e2) (fun _ -> add_exp pid e2 mem loc n_num)
    |> DM.final
  | Strncpy (e1, e2, e3, loc)
  | Memcpy (e1, e2, e3, loc)
  | Memmove (e1, e2, e3, loc) ->
    DM.empty
    |> DM.add (CilHelper.s_exp e1) (fun _ -> add_exp pid e1 mem loc n_num)
    |> DM.add (CilHelper.s_exp e2) (fun _ -> add_exp pid e2 mem loc n_num)
    |> DM.add (CilHelper.s_exp e3) (fun _ -> add_exp pid e3 mem loc n_num)
    |> DM.final

let add_query i q dm =  DM.add (Report.string_of_query q) (fun _ -> add_exps i q) dm

let queries (g, i, o, a) = list_fold (add_query i) a DM.empty |> DM.final

let debug : Global.t * Table.t * Table.t * Report.query list -> unit
  = fun (g, i, o, a) ->
    max_count := ItvDom.Val.get_fp_count ();
    DM.run (queries (g, i, o, a))

