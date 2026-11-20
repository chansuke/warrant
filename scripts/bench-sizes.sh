#!/usr/bin/env bash
# Bench examples/msort.wrt at several input lengths by rewriting `(gen 2000 42)`.
#
#   scripts/bench-sizes.sh [SIZES [RUNS]] [-- options for both run and bench]
#
# SIZES is space separated (default "1000 2000 4000 8000"), RUNS is bench's
# -n (default 3). Options after `--` go to both `run --report` and `bench`,
# so only shared ones such as `--contracts off` belong there. Prints one
# S-expression with the median and the copied vector elements per size.
set -euo pipefail
set -f

pos=()
while [ $# -gt 0 ] && [ "$1" != "--" ]; do pos+=("$1"); shift; done
[ "${1:-}" = "--" ] && shift
sizes=${pos[0]:-1000 2000 4000 8000}
runs=${pos[1]:-3}

fail() { echo "(error :kind usage :msg \"$1\")"; exit 2; }
[[ $runs =~ ^[1-9][0-9]*$ ]] || fail "RUNS must be a positive integer, got $runs"
read -r -a ns <<<"$sizes"
[ ${#ns[@]} -gt 0 ] || fail "SIZES is empty"
for n in "${ns[@]}"; do [[ $n =~ ^[1-9][0-9]*$ ]] || fail "sizes must be positive integers, got $n"; done

root=$(git rev-parse --show-toplevel)
example=$root/examples/msort.wrt
[ "$(grep -c '(gen 2000 42)' "$example")" = 1 ] || fail "examples/msort.wrt no longer calls (gen 2000 42) exactly once"
cargo build --release --quiet --manifest-path "$root/Cargo.toml"
bin=$root/target/release/warrant
work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT

rows=()
for n in "${ns[@]}"; do
  src=$work/msort-$n.wrt
  sed "s/(gen 2000 42)/(gen $n 42)/; s/(wall-ms 500)/(wall-ms 3600000)/" "$example" >"$src"
  median=$("$bin" bench "$src" -n "$runs" "$@" | sed -n 's/.*(wall-ms .*:median \([0-9][0-9.]*\) .*/\1/p')
  elems=$("$bin" run "$src" --report "$@" | sed -n 's/.*(vec-elems \([0-9][0-9]*\)).*/\1/p')
  [ -n "$median" ] && [ -n "$elems" ] || fail "no :median or vec-elems in the output for n=$n"
  rows+=("(n $n :median-ms $median :vec-elems $elems)")
done

printf '(bench-sizes :file "examples/msort.wrt" :runs %s\n' "$runs"
for r in "${rows[@]}"; do printf '  %s\n' "$r"; done
echo ')'
