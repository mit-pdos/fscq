let disk_fn = "disk.img"
let blocksize = Big.of_int 32768

let read_disk b =
  let ic = open_in_gen [Open_rdonly;Open_creat] 0o666 disk_fn in
  seek_in ic b;
  try
    let v = input_byte ic in
    close_in ic;
    (Word.natToWord blocksize (Big.of_int v))
  with
    End_of_file -> close_in ic; (Word.natToWord blocksize (Big.of_int 0))

let write_disk b v =
  let oc = open_out_gen [Open_wronly;Open_creat] 0o666 disk_fn in
  seek_out oc (Big.to_int b);
  output_byte oc (Big.to_int (Word.wordToNat blocksize v));
  close_out oc

let sync_disk b =
  let oc = open_out_gen [Open_wronly;Open_creat] 0o666 disk_fn in
  (* ExtUnix.All.fsync oc; *)
  close_out oc

let rec run_dcode = function
  | Prog.Done t ->
    ()
  | Prog.Trim (a, rx) ->
    Printf.printf "trim(%d)\n" (Big.to_int a);
    run_dcode (rx ())
  | Prog.Sync (a, rx) ->
    Printf.printf "sync(%d)\n" (Big.to_int a);
    sync_disk (Big.to_int a);
    run_dcode (rx ())
  | Prog.Read (a, rx) ->
    let v = read_disk (Big.to_int a) in
    Printf.printf "read(%d)\n" (Big.to_int a);
    run_dcode (rx v)
  | Prog.Write (a, v, rx) ->
    Printf.printf "write(%d)\n" (Big.to_int a);
    write_disk a v;
    run_dcode (rx ());;
