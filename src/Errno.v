Set Implicit Arguments.

Inductive Errno :=
| EINTERNAL
| ENOTDIR
| EISDIR
| ENOENT
| EFBIG
| ENAMETOOLONG
| EEXIST
| ENOSPCBLOCK
| ENOSPCINODE
| ENOTEMPTY
| EOVERFLOW.

Inductive res (T : Type) :=
| OK : T -> res T
| Err : Errno -> res T.

Arguments Err {T} _.

Inductive isError : forall {T : Type}, res T -> Prop :=
| isErrorErr : forall T errno, @isError T (Err errno).

Hint Constructors isError.
