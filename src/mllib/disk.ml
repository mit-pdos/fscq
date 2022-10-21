let block_bytes = 4096

(* counts the number of reads, writes and syncs *)
type stats = {
  mutable reads : int;
  mutable writes : int;
  mutable syncs : int;
}

module IntMap = Map.Make(Int)

type var_store = {
  mutable store : Obj.t IntMap.t;
  mutable nextvar : int;
}

type state = {
  fd : Unix.file_descr;
  stats : stats;
  vars : var_store;
}

let block_to_word b =
  Word.natToWord (Z.of_int (block_bytes * 8)) (Z.of_bits b)

let word_to_string_nbytes nb_bytes (Word.W w) =
  let buf = Bytes.make nb_bytes (Char.chr 0) in
  let bits = Z.to_bits w in
  Bytes.blit_string bits 0 buf 0 (min (String.length bits) nb_bytes);
  Bytes.unsafe_to_string buf

let word_to_string_nbits nb_bits w =
  let nb_bytes = (nb_bits + 7) / 8 in
  word_to_string_nbytes nb_bytes w

let word_to_block w =
  word_to_string_nbytes block_bytes w

let init (filename: string): state =
  let fd = Unix.openfile filename [ Unix.O_RDWR ; Unix.O_CREAT ] 0o666 in
  { fd ;
    stats = { reads = 0; writes = 0; syncs = 0 };
    vars = { store = IntMap.empty; nextvar = 0 } }

let close (st: state) =
  Unix.close st.fd

let print_stats (st: state) =
  Printf.printf "Disk I/O stats:\n";
  Printf.printf "Reads: %d\n" st.stats.reads;
  Printf.printf "Writes: %d\n" st.stats.writes;
  Printf.printf "Syncs: %d\n" st.stats.syncs

let read (st: state) (a: int): Word.word =
  st.stats.reads <- st.stats.reads + 1;
  let buf = Bytes.create block_bytes in
  let cc = ExtUnix.All.pread st.fd (a * block_bytes) buf 0 block_bytes in
  if cc <> block_bytes then (
    Printf.eprintf "attempted read off:%d nbytes:%d\n%!" (a * block_bytes) block_bytes;
    Printf.eprintf "read %d bytes\n%!" cc;
    raise (Failure "Disk.read")
  );
  block_to_word (Bytes.unsafe_to_string buf)

let write (st: state) (a: int) (w: Word.word) =
  st.stats.writes <- st.stats.writes + 1;
  let block = word_to_block w in
  let cc = ExtUnix.All.pwrite st.fd (a * block_bytes) block 0 block_bytes in
  if cc <> block_bytes then raise (Failure "Disk.write")

let sync (st: state) =
  st.stats.syncs <- st.stats.syncs + 1;
  ExtUnix.All.fsync st.fd

let trim (_: state) _ =
  ()

let var_alloc (st: state) (x: Obj.t): int =
  let v = st.vars.nextvar in
  st.vars.nextvar <- st.vars.nextvar + 1;
  st.vars.store <- IntMap.add v x st.vars.store;
  v

let var_get (st: state) (v: int): Obj.t =
  match IntMap.find_opt v st.vars.store with
  | Some x -> x
  | None -> failwith "var_get of unset variable"

let var_set (st: state) (v: int) (x: Obj.t) =
  st.vars.store <- IntMap.add v x st.vars.store

let var_delete (st: state) (v: int) =
  st.vars.store <- IntMap.remove v st.vars.store
