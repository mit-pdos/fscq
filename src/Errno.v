Set Implicit Arguments.

Inductive Errno :=
| ELOGOVERFLOW
| ENOTDIR
| EISDIR
| ENOENT
| EFBIG
| ENAMETOOLONG
| EEXIST
| ENOSPCBLOCK
| ENOSPCINODE
| ENOTEMPTY
| EINVAL.

Inductive res (T : Type) :=
| OK : T -> res T
| Err : Errno -> res T.

Arguments Err {T} _.

Inductive isError : forall {T : Type}, res T -> Prop :=
| isErrorErr : forall T errno, @isError T (Err errno).

Hint Constructors isError.
