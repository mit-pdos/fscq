#!/bin/bash

MAX_PAR=12

info() {
  echo -e "\e[34m$1\e[0m" >&2
}

sep() {
  echo "" >&2
}

addfield() {
  sed $'s/$/\t'"$1/"
}

runbasic() {
  local desc="$1"
  shift

  #echo taskset -c 0-5 parbench "$@"
  parbench "$@" | addfield "$desc"
}

run() {
  local desc="$1"
  shift
  local par="$1"
  shift

  runbasic "$desc" --n=$par +RTS -N$par -qa -RTS "$@"
}

info_system() {
  info "> $system"
}

parse_disk() {
  case $disk in
    mem)
      img="/tmp/disk.img" ;;
    ssd)
      img="/dev/sdg1" ;;
    hdd)
      img="/dev/sda4" ;;
    *)
      echo "invalid disk $disk" >&2
      exit 1
  esac
  if [ -r "$img" ]; then
    img_valid=true
  else
    img_valid=false
  fi
}

setup_cores() {
  local par="$1"
  #local cores=""
  #for core in $(seq 0 2 $(( (par-1)*2 ))); do
  #  cores="$cores,$core"
  #done
  local cores=0-$((par-1))
  sudo dangerously enablecores -c "$cores"
}

# TODO: set this as an exit handler
restore_cores() {
  sudo dangerously enablecores
}

# benchmarks

syscalls() {
  info "syscall baseline"
  for system in fscq cfscq ext4; do
    info_system
    for par in $(seq 1 $MAX_PAR); do
      info "  > n=$par"
      setup_cores $par
      args=( $par "--img=/tmp/disk.img" "--target-ms=500" "--system=$system" )
      run ""            "${args[@]}" statfs --reps=1000
      run ""            "${args[@]}" stat   --reps=10
      run ""            "${args[@]}" open   --reps=10
      run "oob"         "${args[@]}" read   --reps=10 --file="/small" --offset 10000
      run "off-0"       "${args[@]}" read   --reps=10 --file="/small" --offset 0
      run "large"       "${args[@]}" cat-file     --file="/large"
      run "large-dir"   "${args[@]}" traverse-dir --dir="/large-dir"
      run "small files" "${args[@]}" cat-dir      --dir="/large-dir-small-files"
      run ""            "${args[@]}" create
      run ""            "${args[@]}" create-dir
      run ""            "${args[@]}" write
    done
  done
  restore_cores
  sep
}

retry_syscalls() {
  info "retry syscalls"
  for system in fscq cfscq; do
    info_system
    setup_cores 1
    for run in $(seq 1 10); do
      args=( 1 --img="/tmp/disk.img" --system=$system
             --reps=1 --iters=1 --warmup=false )
      run ""          "${args[@]}" open
      run "large-dir" "${args[@]}" traverse-dir --dir="/large-dir"
      run "large"     "${args[@]}" cat-file     --file="/large"
    done
  done
  restore_cores
  sep
}

io_concur() {
  info "I/O concurrency"
  for system in fscq cfscq; do
    info_system
    for par in 1 2; do
      for capabilities in 1 2; do
        setup_cores $capabilities
        for disk in "mem" "ssd" "hdd"; do
          parse_disk
          if [ $img_valid = false ]; then
             continue
          fi
          runbasic "$disk" +RTS -qa -N$capabilities -RTS \
                   --n=$par --system=$system --img=$img \
                   io-concur --reps=25000
        done
      done
    done
  done
  sep
}


dbench() {
  info "dbench"
  for system in fscq cfscq ext4; do
    info_system
    for disk in "mem" "ssd"; do
      parse_disk
      if [ $img_valid = false ]; then
         continue
      fi
      run "$disk" 1 --img="$img" --system=$system \
          dbench --script $HOME/dbench/loadfiles/client.txt
      cp ~/fscq/bench/concurrent/disk.img /tmp/
    done
  done
  sep
}

parsearch() {
  info "par-search"
  for system in fscq cfscq ext4; do
    info_system
    for par in $(seq 1 $MAX_PAR); do
      info "  > n=$par"
      setup_cores $par
      args=( --img=/tmp/disk.img --system=$system
             par-search --dir '/search-benchmarks/coq' --query 'dependency graph'
             --iters=15 )
      run "warmup" $par "${args[@]}" +RTS -A512m -qn8 -RTS
      run "mem"    $par "${args[@]}" +RTS -A512m -qn8 -RTS
    done
  done
  restore_cores
  sep
}

readers_writer() {
  info "readers-writer"
  for par in $(seq 0 $((MAX_PAR-1))); do
    info "> n=$par"
    setup_cores $((par+1))
    args=( --n=$par +RTS -qa -N$((par+1)) -RTS --img=/tmp/disk.img --system=cfscq --iters=5000 )
    runbasic "" "${args[@]}" readers-writer --reps=10 --write-reps=1
    if [ $par -eq 0 ]; then
        runbasic "" "${args[@]}" \
                 +RTS -N1 -RTS \
                 readers-writer --reps=10 --write-reps=1 --only-reads
    fi
  done
  restore_cores
  sep
}

rw_mix() {
  info "rw-mix"
  for par in $(seq 1 $MAX_PAR); do
    info "> n=$par"
    setup_cores $par
    args=( --n=$par +RTS -qa -N$par -RTS --img=/tmp/disk.img --system=cfscq --target-ms=1000 )
    for mix in 0.95 0.9 0.8; do
      runbasic "mix-$mix" "${args[@]}" \
               rw-mix --reps=10 --write-reps=1 --read-perc=$mix
    done
  done
  restore_cores
  sep
}

run_fusebench() {
  for system in fscq cfscq ext4; do
    info_system
    for par in $(seq 1 $MAX_PAR); do
      info "  > n=$par"
      setup_cores $par
      args=( --n=$par --system=$system "$@" )
      fusebench "${args[@]}" --fs-N=1  \
          | addfield "seq_fs"
      cp ~/fscq/bench/concurrent/disk.img /tmp/
      fusebench "${args[@]}" --fs-N=$par  --rts-flags="-qn4" \
          | addfield "par_gc4"
      cp ~/fscq/bench/concurrent/disk.img /tmp/
    done
  done
  restore_cores
  sep
}

ripgrep() {
  info "ripgrep"
  run_fusebench search --dir 'search-benchmarks/coq/core0'
}

mailserver() {
  info "mailserver"
  run_fusebench mailserver --init-messages=0 --read-last=0 --users=48 \
                --read-perc=0.95 --iters=1000 \
                +RTS -qn4 -A512m -RTS

}

mailserver_parbench() {
  info "mailserver-parbench"
  for system in fscq cfscq ext4; do
    info_system
    for par in $(seq 1 $MAX_PAR); do
      info "  > n=$par"
      setup_cores $par
      run "parbench" $par --system=$system \
          mailserver --init-messages=0 --read-last=0 --users=48 \
          --read-perc=0.95 --reps=5000 \
          +RTS -qn4 -A512m -RTS
      cp ~/fscq/bench/concurrent/disk.img /tmp/
    done
  done
  sudo dangerously enablecores
}

parbench print-header | addfield "description"

syscalls
retry_syscalls
io_concur
dbench
parsearch
readers_writer
rw_mix
ripgrep
mailserver
mailserver_parbench
