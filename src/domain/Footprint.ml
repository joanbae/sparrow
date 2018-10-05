module ExpArg =
struct
  type offset =
    | NoOffset
    | FieldOffset of Cil.fieldinfo
    | IndexOffset  of Cil.exp
  and t =
    | Offset of offset * t
    | BaseLoc of Cil.lhost
    | Exp of Cil.exp
    | Fun of string * Cil.exp list
  let to_string_offset = function
    | NoOffset -> "NoOffset"
    | FieldOffset f -> CilHelper.s_offset (Field (f, Cil.NoOffset))
    | IndexOffset i -> CilHelper.s_offset (Index (i, Cil.NoOffset))
  let is_offset = function
    | Offset (_,_) -> true
    | _ -> false
  let rec to_string = function
    | BaseLoc lhost -> CilHelper.s_lhost lhost
    | Exp exp -> CilHelper.s_exp exp
    | Fun (fname, args) -> fname^"("^CilHelper.s_exps args^")"
    | Offset (offset, base) -> to_string_offset offset^" of "^to_string base
end

module Value =
struct
  open BasicDom
  type t = {
    itv: Itv.t;
    powloc: PowLoc.t;
    arrayblk: ArrayBlk.t;
    structblk: StructBlk.t;
    powproc: PowProc.t
  } [@@deriving compare]

  let make itv powloc arrayblk structblk powproc =
    {itv; powloc; arrayblk; structblk; powproc}

  let bot = { itv = Itv.bot; powloc = PowLoc.bot; arrayblk = ArrayBlk.bot; structblk = StructBlk.bot; powproc = PowProc.bot }

  let check_bot x =
     Itv.is_bot x.itv |> fun r -> if not r then r else
       PowLoc.is_empty x.powloc |> fun r -> if not r then r else
         ArrayBlk.is_empty x.arrayblk |> fun r -> if not r then  r else
           StructBlk.is_empty x.structblk |> fun r -> if not r then r else
             PowProc.is_empty x.powproc

  let check_powloc_greater_than_equal_to_two x =
     PowLoc.is_empty x.powloc |> fun r -> if r then not r else
       PowLoc.priority x.powloc |> fun r -> if r = 3 then true else false

  let pp fmt x =
    Format.fprintf fmt "( %a, %a, %a, %a, %a )"
      Itv.pp x.itv
      PowLoc.pp x.powloc
      ArrayBlk.pp x.arrayblk
      StructBlk.pp x.structblk
      PowProc.pp x.powproc
 end

type t = {
  file: string;                  (** The analyzer's fileName **)
  line: int;                     (** Line number in that file **)
  src_location: Cil.location;    (** Describe a location in a C source file **)
  exp : ExpArg.t;
  n_info: string;                 (** Node number **)
  value : Value.t;                (** value **)
  order : int;
  parent : t option;
  addrOf : t option;
  priority : int
}

let rec pp fmt {file; line;
            src_location = {Cil.file = src_file;
                            line = src_line;
                            byte = src_byte};
           exp; n_info; value; order; parent; addrOf; priority} =
  let file_name =  Filename.basename file in
  let exp = ExpArg.to_string exp in 
  Format.fprintf fmt "v:%a ==> %s@%s:%d(%s:%d)@%s, o:%d p:%d"
    Value.pp value exp file_name line src_file src_line n_info order priority;
  let () =
   match parent with
  | None -> ()
  | Some parent ->
    ( Format.fprintf fmt "{ @[ parent:";
      pp fmt parent;
      Format.fprintf fmt "@] }" ) in
   match addrOf with
  | None -> ()
  | Some addr ->
    ( Format.fprintf fmt "{ @[ AddrOf:";
      pp fmt addr;
      Format.fprintf fmt "@] }" )

let to_string x = Format.asprintf "%a" pp x

let compare x y =
  compare x.file y.file |> fun r -> if r <> 0 then r else
    compare x.line y.line |> fun r -> if r <> 0 then r else
      Cil.compareLoc x.src_location y.src_location |> fun r -> if r <> 0 then r else
        compare x.value y.value

let of_here ?(parent=None) ?(addrOf=None) here src_location exp n_info value order priority : t =
  { file = here.Lexing.pos_fname;
    line = here.Lexing.pos_lnum;
    src_location;
    exp;
    n_info;
    value;
    order;
    parent;
    addrOf;
    priority
  }
