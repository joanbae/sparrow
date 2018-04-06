type t = {
  file: string; (** The analyzer's fileName **)
  line: int;    (** Line number in that file **)
  src_location: Cil.location; (** Describe a location in a C source file **)
}

let compare x y =
  compare x.file y.file |> fun r -> if r <> 0 then r else
    compare x.line y.line |> fun r -> if r <> 0 then r else
      Cil.compareLoc x.src_location y.src_location

let pp fmt {file; line;
            src_location = {Cil.file = src_file;
                            line = src_line;
                            byte = src_byte}} =
  Format.fprintf fmt "%s:%d(%s:%d:%d)" file line src_file src_line src_byte

let to_string x =
  pp Format.str_formatter x;
  Format.flush_str_formatter ()

let of_here here src_location : t =
  { file = here.Lexing.pos_fname;
    line = here.Lexing.pos_lnum;
    src_location}
