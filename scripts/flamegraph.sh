#!/usr/bin/env bash
# Sample `warrant run` with perf and write a flame graph.
#
#   scripts/flamegraph.sh [FILE] [OUT.svg] [-- extra warrant run options]
#
# Needs perf (and kernel.perf_event_paranoid <= 1, or root) and inferno
# (`cargo install inferno`). Release builds keep line tables (debug = 1).
set -euo pipefail

file=${1:-examples/msort.wrt}
out=${2:-flamegraph.svg}
shift $(( $# > 2 ? 2 : $# ))
[ "${1:-}" = "--" ] && shift

for tool in perf inferno-collapse-perf inferno-flamegraph; do
  command -v "$tool" >/dev/null || { echo "(error :kind usage :msg \"$tool not found\")"; exit 2; }
done

root=$(git rev-parse --show-toplevel)
cargo build --release --quiet --manifest-path "$root/Cargo.toml"
data=$(mktemp)
trap 'rm -f "$data"' EXIT

perf record --quiet -F 4999 -g --call-graph dwarf -o "$data" -- "$root/target/release/warrant" run "$file" --no-cache "$@" >/dev/null
perf script -i "$data" 2>/dev/null | inferno-collapse-perf | inferno-flamegraph --title "warrant run $file" >"$out"
echo "(flamegraph :file \"$file\" :svg \"$out\")"
