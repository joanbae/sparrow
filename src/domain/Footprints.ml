include PowDom.MakeCPO (Footprint)

let of_here here src_location exp n_num = singleton (Footprint.of_here here src_location exp n_num)

let make file line src_location exp n_num = add { Footprint.file = file; line; src_location; exp; n_num} empty
