# Working on Warrant

Warrant is a verified, parallel language for AI agents, and this repository
is its Rust implementation. Read [docs/architecture.md](docs/architecture.md)
for the module layers, the invariants with the checks that hold them, and the
commands. Read [docs/feature-map.md](docs/feature-map.md) for the names of
features and where each one lives; use those names in commits and pull
requests. Decisions are in the Decision Log of [docs/DESIGN.md](docs/DESIGN.md).
The current work is [docs/HANDOFF_M3.md](docs/HANDOFF_M3.md).

The checks hold the rules. `tests/architecture.rs` checks the layers,
`clippy.toml`, `[lints]` in `Cargo.toml` and `src/lib.rs` cover the banned
APIs, `tests/cli.rs` checks output and exit codes, and
`scripts/check-escape-hatches.sh` checks added lines. When one fails, its
message names the fix. Change the design to pass it. Do not silence the check.

## Before you call a change done

- Work inside `nix develop`, which has the Rust, z3, JDK and elan CI uses.
- Run `scripts/verify`, then read `target/verify/summary.md`. Check each
  `docs/verification.md` item it lists.
- Change to the proof cache, discharge, contract erasure, or `formal/`: run
  `scripts/verify formal`.
- Performance change: run `scripts/verify bench` and put the msort median,
  before and after, in the commit message.
- Commit messages are one line of Conventional Commits.

## Decisions

Ask before changing what a program means. Record a new or changed decision
at the end of the Decision Log in `docs/DESIGN.md`. A new dependency needs a
decision too.

## When a bug is fixed or a review finds something

First ask whether a lint, a type, a test, the architecture check, or a
`docs/verification.md` item can stop it from coming back, and add that.
Write a rule here only when none of them can express it.
