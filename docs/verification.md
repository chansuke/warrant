# Verification checklist

Each item below has a trigger you can read from a diff, a check to run or
write, and the commits behind it. Check only the items whose trigger matches
your change.

```sh
scripts/verification-checklist.sh             # changes since main, uncommitted ones included
scripts/verification-checklist.sh HEAD~3      # changes since another revision
scripts/verification-checklist.sh A~1 A       # the changes of commit A
```

The script reads the `Paths` and `Added lines` of each item. A path is a shell
pattern in which `*` also matches `/`. An added-lines pattern is an extended
regular expression matched against the lines the diff adds.

Before a pull request, run `scripts/verify`. It runs `cargo fmt --check`, clippy and the tests,
checks the added lines for escape hatches (`scripts/check-escape-hatches.sh`),
and prints the items here that the change triggers. `scripts/verify formal` runs
TLC and Lean, `scripts/verify bench` compares msort with the base, and
`scripts/verify full` runs everything. Logs and a summary are kept in
`target/verify/`.

## Adding and removing items

Add an item only when the same mistake reached at least two commits or pull
requests and a diff shows when it applies. Cite the commits. Remove an item
when its code is gone or a test now catches the mistake on its own.

## Items

### Every output is an S-expression with the right exit code

- Paths: `src/main.rs`, `src/diag.rs`, `src/profile.rs`, `src/specdiff.rs`
- Added lines: `println!|print!|ErrorKind::`
- Check: Every stdout line parses with `sexp::parse_all`, and human text goes
  only to stderr. A new error kind goes into `diag::ErrorKind` and into
  `exit_class` in `tests/cli.rs`. A new option goes into the option tables in
  `src/main.rs`.
- Incidents: #7 (a file without `main` exited 1), #8 (`--contrcts off` ran
  in auto mode and exited 0).

### No input makes warrant panic

- Paths: `src/sexp.rs`, `src/wisp.rs`, `src/ast.rs`, `src/types.rs`, `src/rt.rs`, `src/vector.rs`, `src/eval.rs`
- Check: Deep nesting, huge numbers, impossible ranges and sizes end in an
  `(error ...)`, not a panic or a stack overflow. Add the shape to the
  generators in `tests/properties.rs` or a case to `tests/cli.rs`.
- Incidents: `b45df7b` (deep nesting overflowed the stack), `8a407bf` (an
  impossible range panicked), `5f3d7a0` (a line of only `:` did not round
  trip).

### A wrong `proved` must not erase a check

- Paths: `src/smt.rs`, `src/vc.rs`, `src/solver.rs`, `src/cache.rs`, `src/contracts.rs`, `src/verify.rs`
- Check: Run the tests with z3 on PATH; `scripts/verify` says when it was
  not. Names and strings must map to SMT one to one, and a proof result may
  come only from the solver or the user's own cache. Add a program to
  `tests/soundness.rs` or `tests/cli.rs` that a wrong encoding would prove.
- Incidents: `d9b1d68` (backslashes and `|` in names proved wrong
  contracts), `d08c809` (a cache shipped with the source was trusted).

### A new builtin works in every pass

- Paths: `src/builtin.rs`
- Check: Implement it in `rt.rs`, and in `eval.rs` until M2-7 removes it.
  Fill every match the compiler points to (types, effects, VC generation).
  Add a case to `tests/runtime_diff.rs` so the runtime and the M1 oracle
  agree, including on errors.
- Incidents: `3d88aeb` (`all?`), `23719f9` (`perm?`).

### Performance changes carry a measurement

- Paths: `src/rt.rs`, `src/ir.rs`, `src/vector.rs`, `src/profile.rs`
- Check: Run `scripts/verify bench` and put the msort median, before and
  after, in the commit message. CI fails a slowdown over 15%.
- Incidents: `4f3ddb6`, `863c5f9` (#5), `5db11d8` (#6).

### The formal models still describe the code

- Paths: `src/cache.rs`, `src/verify.rs`, `src/contracts.rs`, `formal/*`
- Check: Run `scripts/verify formal`. TLC checks the model, not the code: the
  cache must still write a temporary file and rename it, discharge must
  still take each obligation at most once, and `Checks` must erase only
  proved clauses, as `Warrant.erasure_sound` assumes. If the code changes
  one of these, change the model and keep its negative control failing.
- Incidents: `bfcfb23` (partial cache entries), `e4601bc`, `2600d3b`.
