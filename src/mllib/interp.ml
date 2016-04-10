let addrlen = Big.of_int 64
let blockbytes = 4096
let blockbits = Big.of_int (blockbytes*8)
let disk_fd = ref Unix.stderr   (* just some Unix.file_descr object *)
let disk_in = ref stdin
let disk_out = ref stdout
let debug = true

let addr_to_int a = Big.to_int (Word.wordToNat addrlen a)

let word_to_block (Word.W w) =
  let s = Z.to_bits w in
  let nbytes = String.length s in
  String.concat "" [ s ; String.make (blockbytes-nbytes) (Char.chr 0) ]

let block_to_word b = Word.W (Z.of_bits b)

let init_disk fn =
  let fd = Unix.openfile fn [ Unix.O_RDWR ; Unix.O_CREAT ] 0o666 in
  disk_fd := fd;
  disk_in := Unix.in_channel_of_descr fd;
  disk_out := Unix.out_channel_of_descr fd

let close_disk =
  Unix.close !disk_fd

let read_disk b =
  let ic = !disk_in in
  seek_in ic (b*blockbytes);
  let s = really_input_string ic blockbytes in
  block_to_word s

let write_disk b v =
  let oc = !disk_out in
  seek_out oc (b*blockbytes);
  let s = word_to_block v in
  output_string oc s

let sync_disk b =
  let fd = !disk_fd in
  ExtUnix.All.fsync fd

let rec run_dcode = function
  | Prog.Done t ->
    if debug then Printf.printf "done()\n";
    ()
  | Prog.Trim (a, rx) ->
    if debug then Printf.printf "trim(%d)\n" (addr_to_int a);
    run_dcode (rx ())
  | Prog.Sync (a, rx) ->
    if debug then Printf.printf "sync(%d)\n" (addr_to_int a);
    sync_disk (addr_to_int a);
    run_dcode (rx ())
  | Prog.Read (a, rx) ->
    if debug then Printf.printf "read(%d)\n" (addr_to_int a);
    let v = read_disk (addr_to_int a) in
    run_dcode (rx v)
  | Prog.Write (a, v, rx) ->
    if debug then Printf.printf "write(%d)\n" (addr_to_int a);
    write_disk (addr_to_int a) v;
    run_dcode (rx ())

let run_prog p =
  try
    run_dcode (p (fun x -> Prog.Done x))
  with
    e -> Printf.printf "Exception: %s\n" (Printexc.to_string e)
