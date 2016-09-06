let addrlen = Big.of_int 64
let blockbytes = 4096
let blockbits = Big.of_int (blockbytes*8)
let debug = false
let really_sync = false

type disk_state = { disk_fd : Unix.file_descr ref }

let addr_to_int a = Big.to_int (Word.wordToNat addrlen a)

let word_to_block (Word.W w) =
  let s = Z.to_bits w in
  let nbytes = String.length s in
  let res = String.concat "" [ s ; String.make (blockbytes-nbytes) (Char.chr 0) ] in
  res

let block_to_word b =
  let z = Z.of_bits b in
  Word.W z

let init_disk fn =
  let fd = Unix.openfile fn [ Unix.O_RDWR ; Unix.O_CREAT ] 0o666 in
  { disk_fd = ref fd }

let close_disk { disk_fd = fd } =
  Unix.close !fd

let read_disk { disk_fd = fd } b =
  let s = String.create blockbytes in
  let cc = ExtUnix.All.pread !fd (b * blockbytes) s 0 blockbytes in
  if cc != blockbytes then raise (Failure "read_disk");
  block_to_word s

let write_disk { disk_fd = fd } b v =
  let s = word_to_block v in
  let cc = ExtUnix.All.pwrite !fd (b * blockbytes) s 0 blockbytes in
  if cc != blockbytes then raise (Failure "write_disk")

let sync_disk { disk_fd = fd } b =
  if really_sync then ExtUnix.All.fsync !fd

let set_size_disk { disk_fd = fd } b =
  Unix.ftruncate !fd (b*blockbytes)

let rec run_dcode ds = function
  | Prog.Done t ->
    if debug then Printf.printf "done()\n%!";
    t
  | Prog.Trim (a, rx) ->
    if debug then Printf.printf "trim(%d)\n%!" (addr_to_int a);
    run_dcode ds (rx ())
  | Prog.Sync (a, rx) ->
    if debug then Printf.printf "sync(%d)\n%!" (addr_to_int a);
    sync_disk ds (addr_to_int a);
    run_dcode ds (rx ())
  | Prog.Read (a, rx) ->
    if debug then Printf.printf "read(%d)\n%!" (addr_to_int a);
    let v = read_disk ds (addr_to_int a) in
    run_dcode ds (rx v)
  | Prog.Write (a, v, rx) ->
    if debug then Printf.printf "write(%d)\n%!" (addr_to_int a);
    write_disk ds (addr_to_int a) v;
    run_dcode ds (rx ())

let run_prog ds p =
  try
    run_dcode ds (p (fun x -> Prog.Done x))
  with
    e -> Printf.printf "Exception: %s\n%!" (Printexc.to_string e); raise e
