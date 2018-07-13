include PowDom.MakeCPO (Footprint)

let of_here here src_location exp n_num value order = singleton (Footprint.of_here here src_location exp n_num value order)

let make file line src_location exp n_num value order = add { Footprint.file = file; line; src_location; exp; n_num; value; order} empty

