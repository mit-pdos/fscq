open Fs4;;
open Printf;;

let (r, t) = fs_apply_list buf_init buf_apply [
    (Coq_do_read) ;
    (Coq_do_crash) ;
    (Coq_do_write "a") ;
    (Coq_do_read) ;
    (Coq_do_write "c") ;
    (Coq_do_sync) ;
    (Coq_do_write "b") ;
   ] in
  match r.coq_BufMem with
  | Some x -> Printf.printf "BufMem = %s\n" x
  | None -> Printf.printf "BufMem = <Empty>\n" ;;

