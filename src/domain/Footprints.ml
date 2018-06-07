include PowDom.MakeCPO (Footprint)

let of_here here src_location exp = singleton (Footprint.of_here here src_location exp)

let make file line src_location exp = add { Footprint.file = file; line; src_location; exp} empty
