let addrlen = Big.of_int 64
let blocksize = Big.of_int 32768
let disk_fd = ref Unix.stderr   (* just some Unix.file_descr object *)
let disk_in = ref stdin
let disk_out = ref stdout

let addr_to_int a = Big.to_int (Word.wordToNat addrlen a)

let init_disk fn =
  let fd = Unix.openfile fn [ Unix.O_RDWR ; Unix.O_CREAT ] 0o666 in
  disk_fd := fd;
  disk_in := Unix.in_channel_of_descr fd;
  disk_out := Unix.out_channel_of_descr fd

let close_disk =
  Unix.close !disk_fd

let read_disk b =
  let ic = !disk_in in
  seek_in ic b;
  try
    let v = input_byte ic in
    Word.natToWord blocksize (Big.of_int v)
  with
    End_of_file -> Word.natToWord blocksize (Big.of_int 0)

let write_disk b v =
  let oc = !disk_out in
  seek_out oc b;
  output_byte oc (Big.to_int (Word.wordToNat blocksize v))

let sync_disk b =
  let fd = !disk_fd in
  ExtUnix.All.fsync fd

let rec run_dcode = function
  | Prog.Done t ->
    ()
  | Prog.Trim (a, rx) ->
    Printf.printf "trim(%d)\n" (addr_to_int a);
    run_dcode (rx ())
  | Prog.Sync (a, rx) ->
    Printf.printf "sync(%d)\n" (addr_to_int a);
    sync_disk (addr_to_int a);
    run_dcode (rx ())
  | Prog.Read (a, rx) ->
    Printf.printf "read(%d)\n" (addr_to_int a);
    let v = read_disk (addr_to_int a) in
    run_dcode (rx v)
  | Prog.Write (a, v, rx) ->
    Printf.printf "write(%d)\n" (addr_to_int a);
    write_disk (addr_to_int a) v;
    run_dcode (rx ());;
