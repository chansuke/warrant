#!/usr/bin/env bash
# Tests check-escape-hatches.sh against a throwaway repository.
set -euo pipefail

check=$(cd "$(dirname "$0")" && pwd)/check-escape-hatches.sh
repo=$(mktemp -d)
trap 'rm -rf "$repo"' EXIT
cd "$repo"
export GIT_CONFIG_GLOBAL=/dev/null GIT_CONFIG_NOSYSTEM=1
git init -q -b main
git -c user.name=t -c user.email=t@example.com commit -q --allow-empty -m base
failures=0
expect() { # WANT(pass|fail) DESCRIPTION FILE CONTENT
  local want=$1 what=$2 status=0
  mkdir -p "$(dirname "$3")"
  printf '%s\n' "$4" >"$3"
  git add "$3"
  "$check" --staged >/dev/null 2>&1 || status=$?
  if { [ "$want" = pass ] && [ "$status" -ne 0 ]; } || { [ "$want" = fail ] && [ "$status" -ne 1 ]; }; then
    echo "FAIL: $what (exit $status)"
    failures=1
  fi
  git rm -q --cached "$3"
  rm -f "$3"
}

expect pass "plain code" src/a.rs 'fn main() {}'
expect fail "a TODO comment" src/a.rs 'fn main() {} // TODO: handle errors'
expect fail "a workaround comment" src/a.rs '// Workaround for the flaky test'
expect fail "for now in a script" scripts/a.sh 'sleep 1 # for now'
expect pass "a word in a string, not a comment" src/a.rs 'let s = "TODO list";'
expect pass "a temporary file" src/a.rs '// Write a temporary file, then rename it.'
expect pass "an attribute is not a comment" src/a.rs '#[cfg(test)]'
expect fail "an allow" src/a.rs '#[allow(clippy::unwrap_used)]'
expect fail "an inner allow" src/a.rs '#![allow(dead_code)]'
expect fail "an expect without a reason" src/a.rs '#[expect(clippy::print_stdout)]'
expect pass "an expect with a reason" src/a.rs '#[expect(clippy::print_stdout, reason = "the print builtin")]'
expect fail "an ignored test without a reason" tests/a.rs '#[ignore]'
expect pass "an ignored test with a reason" tests/a.rs '#[ignore = "takes ten minutes"]'
expect fail "an unsafe block" src/a.rs 'let x = unsafe { f() };'
expect pass "unsafe inside a word" src/a.rs 'let unsafe_count = 0;'
expect fail "a shellcheck directive without a reason" scripts/a.sh '# shellcheck disable=SC2086'
expect pass "a shellcheck directive with a reason" scripts/a.sh '# shellcheck disable=SC2086 # word splitting is wanted'
expect pass "prose in docs" docs/usage.md 'For now, only Linux is supported. TODO list'

# A range reports the line number in the new file.
printf 'a\nb\n' >f.rs
git add f.rs
git -c user.name=t -c user.email=t@example.com commit -q -m two
printf 'a\nb\n// TODO c\n' >f.rs
git add f.rs
git -c user.name=t -c user.email=t@example.com commit -q -m three
reported=$("$check" HEAD~1 HEAD 2>&1 || true)
if ! grep -q '^f.rs:3: // TODO c$' <<<"$reported"; then
  echo "FAIL: the line number of an added line"
  failures=1
fi

if [ "$failures" -ne 0 ]; then
  exit 1
fi
