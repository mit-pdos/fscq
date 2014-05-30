open Fs4;;
open Printf;;

fs_apply_list buf_init buf_apply [
    (Coq_do_read) ;
    (Coq_do_crash) ;
    (Coq_do_write "a") ;
    (Coq_do_read) ;
    (Coq_do_write "c") ;
    (Coq_do_write "b") ;
]

