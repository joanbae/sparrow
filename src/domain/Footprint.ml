type t = {
  file: string;                  (** The analyzer's fileName **)
  line: int;                     (** Line number in that file **)
  src_location: Cil.location;    (** Describe a location in a C source file **)
  exp : string;
  n_num: string;                 (** Node number **)
  value : string;                (** value **)
  order : string
}

let compare x y =
  compare x.file y.file |> fun r -> if r <> 0 then r else
    compare x.line y.line |> fun r -> if r <> 0 then r else
      Cil.compareLoc x.src_location y.src_location

let pp fmt {file; line;
            src_location = {Cil.file = src_file;
                            line = src_line;
                            byte = src_byte};
           exp; n_num; value; order} =
  let file_name =  Filename.basename file in
  Format.fprintf fmt "\nv:%s ==>%s@%s:%d(%s:%d:%d)@%s, order:%s" value exp file_name line src_file src_line src_byte n_num order

let to_string x =
  pp Format.str_formatter x;
  Format.flush_str_formatter ()

let of_here here src_location exp n_num value order : t =
  { file = here.Lexing.pos_fname;
    line = here.Lexing.pos_lnum;
    src_location;
    exp;
    n_num;
    value;
    order
  }



