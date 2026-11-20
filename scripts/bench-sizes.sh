#!/usr/bin/env bash
# Bench examples/msort.wrt at several input lengths by rewriting `(gen 2000 42)`.
#
#   scripts/bench-sizes.sh [SIZES] [RUNS] [-- extra warrant bench options]
#
# SIZES is space separated (default "1000 2000 4000 8000"). Prints one
# S-expression with the median and the copied vector elements per size.
set -euo pipefail

sizes=${1:-1000 2000 4000 8000}
runs=${2:-3}
shift $(( $# > 2 ? 2 : $# ))
[ "${1:-}" = "--" ] && shift

root=$(git rev-parse --show-toplevel)
cargo build --release --quiet --manifest-path "$root/Cargo.toml"
bin=$root/target/release/warrant
work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT

rows=()
for n in $sizes; do
  src=$work/msort-$n.wrt
  sed "s/(gen 2000 42)/(gen $n 42)/; s/(wall-ms 500)/(wall-ms 3600000)/" "$root/examples/msort.wrt" >"$src"
  median=$("$bin" bench "$src" -n "$runs" "$@" | sed -n 's/.*(wall-ms .*:median \([0-9.]*\).*/\1/p')
  elems=$("$bin" run "$src" --report "$@" | sed -n 's/.*(vec-elems \([0-9]*\)).*/\1/p')
  rows+=("(n $n :median-ms $median :vec-elems $elems)")
done

printf '(bench-sizes :file "examples/msort.wrt" :runs %s\n' "$runs"
for r in "${rows[@]}"; do printf '  %s\n' "$r"; done
echo ')'
