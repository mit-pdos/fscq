module C = Configurator.V1

let read_file path =
  let in_ch = open_in path in
  let rec loop acc =
    try
      let line = input_line in_ch in
      loop (acc ^ line)
    with End_of_file -> acc
  in
  try
    let result = loop "" in
    close_in in_ch;
    result
  with exc ->
    close_in in_ch;
    Printf.eprintf "read_file: could not read file: '%s'" path;
    raise exc

let () =
  C.main ~name:"foo" (fun c ->
      let default : C.Pkg_config.package_conf =
        { libs = [ "-lfuse" ]; cflags = [] }
      in
      let conf =
        match C.Pkg_config.get c with
        | Some pkgc -> (
            match C.Pkg_config.query pkgc ~package:"fuse" with
            | Some flags -> flags
            | None -> default )
        | None -> default
      in
      let calmidl_fname = "camlidl.libs.sexp" in
      let camlidl_lib_path =
        match
          Sys.command
            (Printf.sprintf "opam var camlidl:lib > %s" calmidl_fname)
        with
        | 0 -> String.trim (read_file calmidl_fname)
        | _ -> (
            match
              Sys.command
                (Printf.sprintf "ocamlfind query camlidl > %s" calmidl_fname)
            with
            | 0 -> String.trim (read_file calmidl_fname)
            | _ -> C.die "Could not query camlidl lib path" )
      in
      let camlidl_libs = [ "-L" ^ camlidl_lib_path; "-lcamlidl" ] in
      C.Flags.(
        write_sexp calmidl_fname camlidl_libs;
        write_sexp "fuse.cflags.sexp" conf.cflags;
        write_sexp "fuse.libs.sexp" conf.libs))
