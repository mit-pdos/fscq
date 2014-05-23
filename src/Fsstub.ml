open Printf;;

(* I/O stubs *)

let file = "fs_disk";;

let _read_disk b =
    let ic = open_in file in
        let s = input_line ic in
        close_in ic;
    s;;

let _write_disk s =
    let oc = open_out file in
        fprintf oc "%s\n" s;
        close_out oc;
    s;;


