type word =
  W of Big.big_int

let wrap sz n =
  Big.modulo n (Big_int.power_int_positive_big_int 2 sz)

let natToWord sz n = W (wrap sz n)
let wordToNat sz (W n) = n
let wzero sz = W Big.zero
let zext sz (W w) sz' = W w

let weq sz (W a) (W b) = Big.eq a b
let wlt_dec sz (W a) (W b) = a < b

let wplus sz (W a) (W b) = W (wrap sz (Big.add a b))
let wminus sz (W a) (W b) = W (wrap sz (Big.sub a b))
let wmult sz (W a) (W b) = W (wrap sz (Big.mult a b))

let combine sz1 (W a) sz2 (W b) = W (Big.add a (Big_int.shift_left_big_int b (Big.to_int sz1)))
let split1 sz1 sz2 (W a) = W (wrap sz1 a)
let split2 sz1 sz2 (W a) = W (Big_int.shift_right_big_int a (Big.to_int sz1))
let splice _ _ _ _ _ _ = raise Not_found
