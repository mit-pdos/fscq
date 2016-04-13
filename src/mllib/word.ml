type word =
  W of Big.big_int

let wrap sz n =
  let isz = Z.to_int sz in
  if isz == 0 then Z.zero else Z.extract n 0 isz

let two_to_n n = Z.shift_left Z.one (Z.to_int n)

let natToWord sz n = W (wrap sz n)
let wordToNat sz (W n) = n
let wzero sz = W Big.zero
let zext sz (W w) sz' = W w

let weq sz (W a) (W b) = Big.eq a b
let wlt_dec sz (W a) (W b) = a < b

let wplus sz (W a) (W b) = W (wrap sz (Big.add a b))
let wminus sz (W a) (W b) = W (wrap sz (Big.sub (Big.add (two_to_n sz) a) b))
let wmult sz (W a) (W b) = W (wrap sz (Big.mult a b))
let wdiv sz (W a) (W b) = W (Big.div a b)
let wmod sz (W a) (W b) = W (Big.modulo a b)

let wbit sz _ (W n) =
  let int_n = Z.to_int n in
  if int_n >= (Z.to_int sz)
    then W Z.zero
    else W (Z.shift_left Z.one int_n)
let wor _ (W a) (W b) = W (Big_int_Z.or_big_int a b)
let wand _ (W a) (W b) = W (Big_int_Z.and_big_int a b)

let combine sz1 (W a) sz2 (W b) = W (Big.add a (Big_int_Z.shift_left_big_int b (Big.to_int sz1)))
let split1 sz1 sz2 (W a) = W (wrap sz1 a)
let split2 sz1 sz2 (W a) = W (Big_int_Z.shift_right_big_int a (Big.to_int sz1))
let splice _ _ _ _ _ _ = raise Not_found
