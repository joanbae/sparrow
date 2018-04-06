include PowDom.MakeCPO (Footprint)

let of_here here src_location = singleton (Footprint.of_here here src_location)

let make file line src_location = add { Footprint.file = file; line; src_location } empty
