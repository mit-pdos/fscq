# - coqide compilation can be disabled by setting lablgtk to null;

{stdenv, fetchgit, writeText, pkgconfig, ocaml, findlib, camlp5, ncurses, lablgtk ? null}:

let
  version = "fscq_2015-08-28";
  coq-version = "8.5";
  buildIde = lablgtk != null;
  ideFlags = if buildIde then "-lablgtkdir ${lablgtk}/lib/ocaml/*/site-lib/lablgtk2 -coqide opt" else "";
in

stdenv.mkDerivation {
  name = "coq-${version}";

  inherit coq-version;
  inherit ocaml camlp5;

  src = fetchgit {
    url = https://github.com/coq/coq.git;
    rev = "76d6a8cfb0448ade98e1a7abc92ff1bf5075fe8f"; # suggested eaa... didn't work
    sha256 = "90a87f6f710fc82e0d1a08c66dcb8b6b328bbc0492c76f7e4f1745cdddcd9383"; # "aae8efee973134a2a6d6306fc65def147f646020becde741b2b9473456949172";
  };

  buildInputs = [ pkgconfig ocaml findlib camlp5 ncurses lablgtk ];

  patches = [ ./no-codesign.patch ];

  postPatch = ''
    UNAME=$(type -tp uname)
    RM=$(type -tp rm)
    substituteInPlace configure --replace "/bin/uname" "$UNAME"
    substituteInPlace tools/beautify-archive --replace "/bin/rm" "$RM"
    substituteInPlace Makefile.build --replace "ifeq (\$(ARCH),Darwin)" "ifeq (\$(ARCH),Darwinx)"
  '';

  setupHook = writeText "setupHook.sh" ''
    addCoqPath () {
      if test -d "''$1/lib/coq/${coq-version}/user-contrib"; then
        export COQPATH="''${COQPATH}''${COQPATH:+:}''$1/lib/coq/${coq-version}/user-contrib/"
      fi
    }

    envHooks=(''${envHooks[@]} addCoqPath)
  '';

  preConfigure = ''
    configureFlagsArray=(
      -opt
      ${ideFlags}
    )
  '';

  prefixKey = "-prefix ";

  buildFlags = "revision coq coqide";

  meta = with stdenv.lib; {
    description = "Coq proof assistant";
    longDescription = ''
      Coq is a formal proof management system.  It provides a formal language
      to write mathematical definitions, executable algorithms and theorems
      together with an environment for semi-interactive development of
      machine-checked proofs.
    '';
    homepage = "http://coq.inria.fr";
    license = licenses.lgpl21;
    branch = coq-version;
    maintainers = with maintainers; [ roconnor thoughtpolice vbgl ];
    platforms = platforms.unix;
  };
}
