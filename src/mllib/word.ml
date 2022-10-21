type word =
  W of Big.big_int [@@unboxed]

let wrap sz n =
  let isz = Z.to_int sz in
  if isz == 0 then Z.zero else Z.extract n 0 isz

let two_to_n n = Z.shift_left Z.one (Z.to_int n)

let natToWord sz n = W (wrap sz n)
let wordToNat _sz (W n) = n
let wzero _sz = W Big.zero
let wone _sz = W Big.one
let zext _sz (W w) _sz' = W w

let weq _sz (W a) (W b) = Big.eq a b
let wlt_dec _sz (W a) (W b) = a < b
let bit_dec (W w) = Z.equal w Z.zero

let wplus sz (W a) (W b) = W (wrap sz (Big.add a b))
let wminus sz (W a) (W b) = W (wrap sz (Big.sub (Big.add (two_to_n sz) a) b))
let wmult sz (W a) (W b) = W (wrap sz (Big.mult a b))
let wdiv _sz (W a) (W b) = W (Big.div a b)
let wmod _sz (W a) (W b) = W (Big.modulo a b)

let wbit sz _ (W n) =
  let int_n = Z.to_int n in
  if int_n >= (Z.to_int sz)
    then W Z.zero
    else W (Z.shift_left Z.one int_n)
let wor _sz (W a) (W b) = W (Big_int_Z.or_big_int a b)
let wand _sz (W a) (W b) = W (Big_int_Z.and_big_int a b)
let wlshift _sz (W a) n =
  W (Big_int_Z.shift_left_big_int a (Z.to_int n))
let wrshift _sz (W a) n = W (Big_int_Z.shift_right_big_int a (Z.to_int n))
let wones n =
  W (Z.(pred (one lsl (Z.to_int n))))
let wnot _n (W a) = W (Z.lognot a)

let combine sz1 (W a) _sz2 (W b) =
  W (Z.logor a (Big_int_Z.shift_left_big_int b (Big.to_int sz1)))
let split1 sz1 _sz2 (W a) =
  W (wrap sz1 a)
let split2 sz1 _sz2 (W a) =
  W (Big_int_Z.shift_right_big_int a (Big.to_int sz1))

let splice _ _ _ _ _ _ = raise Not_found

let pow2 = two_to_n
