#!/usr/bin/env bash
# Model-check every spec with TLC. Each model is listed with the outcome it
# must have: `ok`, or the invariant it must violate (a negative control that
# shows the property depends on the mechanism the spec is about).
#
#   formal/tla/check.sh            # uses $TLA2TOOLS, else downloads the jar
set -euo pipefail
cd "$(dirname "$0")"

version=v1.7.4
sha256=936a262061c914694dfd669a543be24573c45d5aa0ff20a8b96b23d01e050e88
jar=${TLA2TOOLS:-}
if [ -z "$jar" ]; then
  jar=${XDG_CACHE_HOME:-$HOME/.cache}/warrant/tla2tools-$version.jar
  if [ ! -f "$jar" ]; then
    mkdir -p "$(dirname "$jar")"
    curl -sSfL -o "$jar.part" "https://github.com/tlaplus/tlaplus/releases/download/$version/tla2tools.jar"
    echo "$sha256  $jar.part" | sha256sum -c --quiet
    mv "$jar.part" "$jar"
  fi
fi

models=(
  "MCProofCache.tla MCProofCache.cfg ok"
  "MCProofCache.tla MCProofCacheInPlace.cfg Sound"
  "Discharge.tla Discharge.cfg ok"
  "Discharge.tla DischargeUnlocked.cfg AtMostOnce"
)

status=0
for m in "${models[@]}"; do
  read -r spec cfg want <<<"$m"
  out=$(java -XX:+UseParallelGC -cp "$jar" tlc2.TLC -workers auto -metadir "$(mktemp -d)" -config "$cfg" "$spec" 2>&1 || true)
  if grep -q "No error has been found" <<<"$out"; then got=ok
  else got=$(sed -n 's/^Error: Invariant \(.*\) is violated.*/\1/p' <<<"$out" | head -1); got=${got:-error}
  fi
  states=$(sed -n 's/.* \([0-9]*\) distinct states found.*/\1/p' <<<"$out" | tail -1)
  verdict=$([ "$got" = "$want" ] && echo pass || echo FAIL)
  echo "(tlc :config $cfg :want $want :got $got :distinct-states ${states:-0} :$verdict)"
  if [ "$verdict" != pass ]; then status=1; echo "$out" | tail -30 >&2; fi
done
exit $status
