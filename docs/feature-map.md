# Feature map

The names of Warrant's features and where each one lives. Use these names in
commits and pull requests. `docs/architecture.md` describes each module.

| Feature | Command or flag | Code | Tests and models |
|---|---|---|---|
| Canonical syntax | every command reads `.wrt` | `sexp.rs` | `tests/properties.rs`, `sexp.rs` |
| Wisp view | `fmt`, reading `.wisp` | `wisp.rs` | `tests/m0.rs`, `tests/properties.rs` |
| Lowering and name resolution | `check`, `run`, `bench` | `ast.rs` | `ast.rs` |
| Type checking | `check`, `run`, `bench` (`--no-typecheck` skips) | `types.rs` | `types.rs`, `tests/cli.rs` |
| Effect checking | `check`, `run`, `bench` | `effects.rs`, and at run time `rt.rs` | `effects.rs`, `tests/m0.rs` |
| Contract proofs | `check` | `vc.rs`, `smt.rs`, `solver.rs`, `verify.rs` | `vc.rs`, `tests/soundness.rs` |
| Parallel discharge | `--jobs` | `verify::discharge` | `formal/tla/Discharge.tla` |
| Proof cache | `--no-cache`, `--cache-dir` | `cache.rs` | `cache.rs`, `tests/cli.rs`, `formal/tla/MCProofCache.tla` |
| Contract erasure | `--contracts auto\|runtime\|off` | `verify::levels`, `contracts::Checks`, `ir.rs` | `verify.rs`, `formal/lean` (`erasure_sound`) |
| IR runtime | `run`, `bench` | `ir.rs`, `rt.rs`, `value.rs` | `tests/runtime_diff.rs`, `tests/copies.rs` |
| Fork-join | `run --threads`, `bench --threads` | `ir::forks`, `rt::Interp::fork_args`, `rt::Pool` | `tests/runtime_diff.rs`, `tests/cli.rs` |
| M1 oracle | none (tests only) | `eval.rs` | `tests/runtime_diff.rs` |
| Profiler report | `run --report` | `profile.rs` | `tests/cli.rs`, `tests/runtime_diff.rs` |
| Budgets | `bench` (exit 3) | `main.rs` (`bench`), `ast.rs` (`:budget`) | `tests/cli.rs` |
| Spec diff | `spec-diff` | `specdiff.rs` | `specdiff.rs`, `tests/cli.rs` |
| Errors and exit codes | every command | `diag.rs` (`ErrorKind`), `main.rs` | `tests/cli.rs` |
