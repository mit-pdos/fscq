#!/usr/bin/env bash

info() {
    echo -e "\e[34m$1\e[0m"
}

sep() {
    echo ""
}

bench() {
    bencher --scalability --n=6 --RTS -- "$@"
}

info "==> metadata-only"
info "statfs"
bench --target-ms=500 --reps=10000 statfs "$@"
sep

info "stat"
bench --target-ms=500 --reps=10000 stat "$@"
sep

info "open"
bench --target-ms=500 --reps=10000 open "$@"
sep

info "read oob"
bench --target-ms=500 --reps=10 read --file '/small' --offset 10000 "$@"
sep

info "readdir medium"
bench --target-ms=500 --reps=10 readdir --dir '/medium-dir' "$@"
sep

info "readdir large"
bench --target-ms=500 --reps=10 readdir --dir '/large-dir/dir1' "$@"
sep

info "traverse large file directory"
bench --target-ms=500 --reps=10 traverse-dir --dir '/large-dir' "$@"
sep

info "==> reading data"
#info "cat linux.tar.xz"
#bench --iters=1 --reps=4 cat-file --file '/linux-source/linux.tar.xz' "$@"
#sep

info "read 0"
bench --target-ms=500 --reps=10 read --file '/large' --offset 0 "$@"
sep

info "read indirect"
bench --target-ms=500 --reps=10 read --file '/large' --offset 62000 "$@"
sep

info "read far"
bench --target-ms=500 --reps=10 read --file '/large' --offset 10000000 "$@"
sep

info "cat large"
bench --target-ms=500 --reps=1 cat-file --file '/large' "$@"
sep

info "cat large file directory"
bench --target-ms=500 --reps=2 cat-dir --dir '/large-dir' "$@"
sep

info "cat small file directory"
bench --target-ms=500 --reps=5 cat-dir --dir '/large-dir-small-files' "$@"
