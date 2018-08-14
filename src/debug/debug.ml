open Vocab
open ItvDom

module DM = Debugmode
module Analysis = SparseAnalysis.Make(ItvSem)
module Table = Analysis.Table

let add_lv pid lv mem loc n_num =
  let (powloc, fp) = ItvSem.eval_lv_with_footprint pid lv mem loc n_num in
  DM.long (fun () ->
      BasicDom.PowLoc.pp Format.err_formatter powloc;
      Format.fprintf Format.err_formatter "@\n=======@\n";
      Footprints.pp Format.err_formatter fp
    )

let remove_fps v =
  let max_count = Val.get_fp_count () in
  let v_only = Val.without_fp v in
  let newFP = Footprints.filter (fun fp -> if int_of_string (fp.order) < max_count  then true else false) (Val.footprints_of_val v) in
  Val.modify_fp_only v_only newFP
  
let add_exp pid e mem loc n_num =
  print_endline("e is "^CilHelper.s_exp e);
  print_endline("mem is"^ItvDom.Mem.to_string mem);
  let v = remove_fps (ItvSem.eval pid e mem loc n_num) in
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
  = fun (g, i, o, a) -> DM.run (queries (g, i, o, a))

