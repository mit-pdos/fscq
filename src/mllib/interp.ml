module Crc32 = Checkseum.Crc32

let verbose = false
let output = false

let debugmsg msgf =
  if verbose then msgf (Printf.kprintf print_endline)

let crc32_word_update c sz w =
  let bits = Disk.word_to_string_nbits sz w in
  Crc32.digest_string bits 0 (String.length bits) c

let rec run : type a. Disk.state -> a Prog.prog -> Obj.t =
  fun ds p ->
  match p with
  | Ret x ->
    debugmsg (fun m -> m "Done");
    Obj.repr x
  | Read a ->
    debugmsg (fun m -> m "Read %s" (Z.to_string a));
    Obj.repr @@ Disk.read ds (Z.to_int a)
  | Write (a, v) ->
    debugmsg (fun m -> m "Write %s" (Z.to_string a));
    Obj.repr @@ Disk.write ds (Z.to_int a) v
  | Sync ->
    debugmsg (fun m -> m "Sync");
    Obj.repr @@ Disk.sync ds
  | Trim a ->
    debugmsg (fun m -> m "Trim %s" (Z.to_string a));
    Obj.repr @@ Disk.trim ds a
  | VarAlloc v ->
    debugmsg (fun m -> m "VarAlloc");
    Obj.repr @@ Disk.var_alloc ds v
  | VarDelete i ->
    debugmsg (fun m -> m "VarDelete %d" i);
    Obj.repr @@ Disk.var_delete ds i
  | VarGet i ->
    debugmsg (fun m -> m "VarGet %d" i);
    Obj.repr @@ Disk.var_get ds i
  | VarSet (i, v) ->
    debugmsg (fun m -> m "VarSet %d" i);
    Obj.repr @@ Disk.var_set ds i v
  | AlertModified ->
    debugmsg (fun m -> m "AlertModified");
    Obj.repr ()
  | Debug (s, n) ->
    if output then
      Printf.printf "%s %s\n%!"
        (String.of_seq (List.to_seq s)) (Z.to_string n);
    Obj.repr ()
  | Rdtsc ->
    (* TODO *)
    Obj.repr Z.zero
  | Hash (sz, w) ->
    debugmsg (fun m -> m "Hash %s" (Z.to_string sz));
    let c = crc32_word_update Crc32.default (Z.to_int sz) w in
    Obj.repr @@ Z.of_int64 (Optint.to_int64 c)
  | Hash2 (sz1, sz2, w1, w2) ->
    debugmsg (fun m -> m "Hash2 %s %s" (Z.to_string sz1) (Z.to_string sz2));
    let c1 = crc32_word_update Crc32.default (Z.to_int sz1) w1 in
    let c2 = crc32_word_update c1 (Z.to_int sz2) w2 in
    Obj.repr @@ Z.of_int64 (Optint.to_int64 c2)
  | Bind (p1, p2) ->
    debugmsg (fun m -> m "Bind");
    let r1 = run ds p1 in
    run ds (p2 r1)

let run (ds: Disk.state) (p: 'a Prog.prog): 'a =
  Obj.magic (run ds p)
