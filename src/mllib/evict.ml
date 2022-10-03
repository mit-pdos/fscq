type eviction_state = unit

let eviction_init = ()

let eviction_update s _ = s

let eviction_choose s = (Z.zero, s)
