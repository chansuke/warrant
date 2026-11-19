#!/usr/bin/env bash
# Compare `warrant bench` medians of a base revision and the working tree.
# Runs alternate between the two builds so machine drift hits both equally.
#
#   scripts/bench-compare.sh BASE_REV [FILE] [ROUNDS] [MAX_SLOWDOWN_PCT]
#
# Prints one S-expression and exits 1 if the median of the round medians
# got slower than MAX_SLOWDOWN_PCT (default 10).
set -euo pipefail

base_rev=${1:?usage: bench-compare.sh BASE_REV [FILE] [ROUNDS] [MAX_SLOWDOWN_PCT]}
file=${2:-examples/msort.wrt}
rounds=${3:-5}
max_pct=${4:-10}

root=$(git rev-parse --show-toplevel)
work=$(mktemp -d)
trap 'git -C "$root" worktree remove --force "$work/base" >/dev/null 2>&1 || true; rm -rf "$work"' EXIT

git -C "$root" worktree add --detach --quiet "$work/base" "$base_rev"
cargo build --release --quiet --manifest-path "$work/base/Cargo.toml"
cargo build --release --quiet --manifest-path "$root/Cargo.toml"

median_of() {
  "$1" bench "$root/$file" -n 10 --no-cache | sed -n 's/.*(wall-ms .*:median \([0-9.]*\).*/\1/p'
}

base=() head=()
for _ in $(seq "$rounds"); do
  base+=("$(median_of "$work/base/target/release/warrant")")
  head+=("$(median_of "$root/target/release/warrant")")
done

mid() { printf '%s\n' "$@" | sort -g | awk '{a[NR]=$1} END {print (NR%2) ? a[(NR+1)/2] : (a[NR/2]+a[NR/2+1])/2}'; }
b=$(mid "${base[@]}")
h=$(mid "${head[@]}")
pct=$(awk -v b="$b" -v h="$h" 'BEGIN {printf "%.1f", (h - b) * 100 / b}')
status=$(awk -v p="$pct" -v m="$max_pct" 'BEGIN {print (p > m) ? "regressed" : "ok"}')

echo "(bench-compare :file \"$file\" :base \"$base_rev\" :rounds $rounds :base-median-ms $b :head-median-ms $h :change-pct $pct :max-pct $max_pct :status $status)"
[ "$status" = ok ]
