#!/usr/bin/env bash
# Install the pinned z3 release (Z3_VERSION, Z3_SHA256) onto the PATH.
set -euo pipefail
name="z3-$Z3_VERSION-x64-glibc-2.39"
curl -sSfLO "https://github.com/Z3Prover/z3/releases/download/z3-$Z3_VERSION/$name.zip"
echo "$Z3_SHA256  $name.zip" | sha256sum -c
unzip -q "$name.zip"
echo "$PWD/$name/bin" >> "$GITHUB_PATH"
"$name/bin/z3" --version
