open Printf;;

(* I/O stubs *)

let file = "fs_disk";;

let _read_disk st addr =
    let ic = open_in file in
        let v = input_line ic in
        close_in ic;
    v;;

let _write_disk st addr v =
    let oc = open_out file in
        fprintf oc "%s\n" v;
        close_out oc;
    st;;


