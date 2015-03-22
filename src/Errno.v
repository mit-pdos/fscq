Inductive Errno :=
| EINVAL
| ENOTDIR
| EISDIR
| ENOENT
| EFBIG
| ENAMETOOLONG
| EEXIST
| ENOSPC
| ENOTEMPTY
| EOVERFLOW.

Inductive res (T : Type) :=
| OK : T -> res T
| Err : Errno -> res T.
