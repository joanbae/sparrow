type t = {
  file: string;                  (** The analyzer's fileName **)
  line: int;                     (** Line number in that file **)
  src_location: Cil.location;    (** Describe a location in a C source file **)
  exp : string;
  n_num: string;                 (** Node number **)
  value : string;                (** value **)
  order : int;
  priority : int;                (** Priority **)
}

let compare x y =
  compare x.file y.file |> fun r -> if r <> 0 then r else
    compare x.line y.line |> fun r -> if r <> 0 then r else
      Cil.compareLoc x.src_location y.src_location |> fun r -> if r <> 0 then r else
        compare x.value y.value


let pp fmt {file; line;
            src_location = {Cil.file = src_file;
                            line = src_line;
                            byte = src_byte};
           exp; n_num; value; order; priority} =
  let file_name =  Filename.basename file in
  let p = string_of_int priority in
  let order = string_of_int order in
  Format.fprintf fmt "v:%s ==> %s@%s:%d(%s:%d:%d)@%s, o:%s p:%s" value exp file_name line src_file src_line src_byte n_num order p

let to_string x =
  pp Format.str_formatter x;
  Format.flush_str_formatter ()

let of_here here src_location exp n_num value order priority : t =
  { file = here.Lexing.pos_fname;
    line = here.Lexing.pos_lnum;
    src_location;
    exp;
    n_num;
    value;
    order;
    priority
  }



