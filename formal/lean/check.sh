#!/usr/bin/env bash
# Build the Lean proofs and make sure the main theorem rests only on Lean's
# standard axioms (no `sorry`).
set -euo pipefail
cd "$(dirname "$0")"
lake build
probe=$(mktemp --suffix .lean)
trap 'rm -f "$probe"' EXIT
printf 'import WarrantFormal\n#print axioms Warrant.erasure_sound\n' >"$probe"
axioms=$(lake env lean "$probe")
echo "$axioms"
if grep -q sorryAx <<<"$axioms"; then echo "(error :kind proof :msg \"erasure_sound uses sorry\")"; exit 1; fi
