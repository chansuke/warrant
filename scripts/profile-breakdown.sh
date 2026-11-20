#!/usr/bin/env bash
# Sample `warrant bench` with perf and break the time down by what the
# interpreter was doing: copying vectors, freeing them, allocating, or
# interpreting. Also writes a flame graph of the same samples.
#
#   scripts/profile-breakdown.sh [FILE] [OUT.svg] [RUNS]
#
# Needs perf (kernel.perf_event_paranoid <= 1) and inferno. Each sample is
# attributed to the frame nearest the leaf that matches a category, so an
# inlined `Value::clone` under `Vec::extend` counts as copying. The patterns
# match the M1 interpreter (`eval.rs`) and change with it.
set -euo pipefail

file=${1:-examples/msort.wrt}
out=${2:-flamegraph.svg}
runs=${3:-20}

for tool in perf inferno-collapse-perf inferno-flamegraph; do
  command -v "$tool" >/dev/null || { echo "(error :kind usage :msg \"$tool not found\")"; exit 2; }
done

root=$(git rev-parse --show-toplevel)
cargo build --release --quiet --manifest-path "$root/Cargo.toml"
work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT

perf record --quiet -F 4999 -g --call-graph dwarf -o "$work/perf.data" -- \
  "$root/target/release/warrant" bench "$file" -n "$runs" --contracts off >/dev/null 2>&1
perf script -i "$work/perf.data" 2>/dev/null | inferno-collapse-perf | grep '^warrant;' >"$work/stacks"
inferno-flamegraph --title "warrant bench $file --contracts off" <"$work/stacks" >"$out"

awk -v file="$file" -v svg="$out" '
function category(f) {
  if (f ~ /extend_trusted/) return "copy-extend"
  if (f ~ /to_vec/) return "copy-to-vec"
  if (f ~ /drop_slow/ || (f ~ /drop_in_place/ && f ~ /Value/)) return "free"
  if (f ~ /^(_int_malloc|malloc|_int_free|cfree.*|free|malloc_consolidate|unlink_chunk.*|_int_realloc|realloc)$/) return "alloc"
  if (f ~ /[Hh]ash/ && f ~ /warrant/) return "name-lookup"
  if (f ~ /Env6lookup|Env4bind/) return "env"
  if (f ~ /Interp7builtin/) return "builtin"
  if (f ~ /Interp7call_fn|Interp5apply|call_body/) return "call"
  if (f ~ /Interp4eval/) return "eval"
  return ""
}
{
  w = $NF; sub(/ [0-9]+$/, ""); n = split($0, fr, ";")
  total += w; hit = "other"
  for (i = n; i >= 1; i--) { c = category(fr[i]); if (c != "") { hit = c; break } }
  pct[hit] += w
}
END {
  printf "(profile-breakdown :file \"%s\" :svg \"%s\"", file, svg
  split("copy-extend copy-to-vec free alloc eval builtin call env name-lookup other", order, " ")
  for (i = 1; i <= 10; i++) printf " :%s-pct %.1f", order[i], 100 * pct[order[i]] / total
  print ")"
}' "$work/stacks"
