include PowDom.MakeCPO (Footprint)

let of_here here src_location exp n_num value = singleton (Footprint.of_here here src_location exp n_num value)

let make file line src_location exp n_num value = add { Footprint.file = file; line; src_location; exp; n_num; value} empty

