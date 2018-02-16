#!/usr/bin/env bash

info() {
    echo -e "\e[34m$1\e[0m"
}

sep() {
    echo ""
}

bench() {
    bencher --n=4 --RTS -- "$@"
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

info "traverse large file directory"
bench --target-ms=500 --reps=10 traverse-dir --dir '/large-dir' "$@"
sep

info "==> reading data"
#info "cat linux.tar.xz"
#bench --iters=1 --reps=4 cat-file --file '/linux-source/linux.tar.xz' "$@"
#sep

info "cat large"
bench --target-ms=500 --reps=1 cat-file --file '/large' "$@"
sep

info "cat large file directory"
bench --target-ms=500 --reps=2 cat-dir --dir '/large-dir' "$@"
sep

info "cat small file directory"
bench --target-ms=500 --reps=5 cat-dir --dir '/large-dir-small-files' "$@"
