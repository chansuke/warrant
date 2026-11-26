# アーキテクチャ

Warrant の処理系は 1 つのクレートで、依存は fork-join のスケジューラ `rayon` だけ（D26、D30）。`src/` のモジュールは下の層から順に積み上がる。設計判断は `docs/DESIGN.md` の Decision Log にある。

## 層

モジュールは自分より下の層のモジュールだけを使う。`tests/architecture.rs` の `LAYERS` が正本で、上や横の層を使うとテストが落ちる。`lib.rs` と `main.rs` はすべての上に立つ。

| 層 | モジュール |
|---|---|
| 0 | `sexp`, `builtin` |
| 1 | `diag`, `wisp`, `profile` |
| 2 | `ast` |
| 3 | `types`, `effects`, `contracts` |
| 4 | `smt` |
| 5 | `solver` |
| 6 | `vc`, `cache` |
| 7 | `verify` |
| 8 | `specdiff`, `ir` |
| 9 | `value` |
| 10 | `rt` |

実行系（`ir`, `value`, `rt`）は証明系（`smt`, `solver`, `vc`, `verify`）を使わない。証明の結果は `verify::levels` が `contracts::ClauseLevels` にして渡す。

## モジュール

| ファイル | 役割 |
|---|---|
| `src/sexp.rs` | 字句解析・構文解析（位置付きエラー、`SpanTree`）、`flat` / `pretty` 表示、`is_clause` |
| `src/wisp.rs` | Wisp 表示の印字と構文解析（可逆、`parse_spanned`） |
| `src/ast.rs` | `lower`: defn と節の解析、名前解決、型注釈の解析。静的検査はすべてここの `Module` を読む |
| `src/builtin.rs` | 組み込み関数の `enum Builtin` と名前の対応 |
| `src/diag.rs` | 静的検査のエラー `Diag`（`:at` 付きの S式）と実行時のエラー `RtError` |
| `src/types.rs` | 静的な型検査（関数内の単相推論、組み込みの多相は使う箇所ごとに実体化） |
| `src/effects.rs` | 静的なエフェクト検査（呼び出しグラフの不動点、関数値の潜在エフェクト） |
| `src/smt.rs` | SMT-LIB の語彙（前置き、ベクタのデータ型、`in64`、`tdiv`、`sorted-VI`、長さの上限） |
| `src/vc.rs` | 記号実行による VC 生成。1つの `Obligation` が1つの完結したスクリプト |
| `src/solver.rs` | `trait Solver` と `Z3`（`z3 -in` のサブプロセス、`get-value` で反例を読む） |
| `src/verify.rs` | VC を並列にソルバに渡し（キャッシュ経由）、`(smt ...)` の集計を作る。結果から節ごとのレベルを決める `levels` |
| `src/contracts.rs` | 節ごとの検証レベル（proved / runtime-checked）の型と、モードから実行時に検査する節を決める `Checks` |
| `src/specdiff.rs` | 仕様差分ガード。節ごとの変更と判定（weakened / strengthened / refined / new）、精緻化の SMT 証明 |
| `src/cache.rs` | VC 単位の証明キャッシュ（既定 `~/.cache/warrant/proofs`、キーはソルバの fingerprint とスクリプト） |
| `src/ir.rs` | 実行用 IR。`Program::new` が `Module` をスロットの環境にコンパイルし、`Checks` が残す節だけを含める |
| `src/value.rs` | IR のランタイムの値 `Value` とベクタ。共有バッファと範囲、参照が1つのときだけその場で書く `cons` / `concat` |
| `src/rt.rs` | IR の評価器 `Interp`（契約、エフェクト、組み込み関数）。`run` / `bench` はこれを使う |
| `src/profile.rs` | `Profiler` と `report`（S式出力） |
| `src/main.rs` | CLI。大きいスタックのスレッドで実行し、終了コードを返す |
| `tests/m0.rs` | 例題の往復・実行・エラー種別の統合テスト |
| `tests/cli.rs` | バイナリを動かす出力形式・終了コードのテスト |
| `tests/properties.rs` | ランダムな正規形の往復、フロントエンドが panic しないこと |
| `tests/soundness.rs` | proved な関数が実行時に失敗しないことの差分テスト（z3 が必要） |
| `tests/runtime_diff.rs` | IR のランタイムの差分テスト。1スレッドと4スレッドの値、エラー、プロファイラのカウンタを、M1 のインタプリタが一致を確かめた期待値 `tests/runtime_diff.golden` と比べる（M2-7） |
| `formal/` | Lean（契約省略の健全性）と TLA+（証明キャッシュ、並列 discharge） |
| `examples/` | `msort`（目標プログラム）、`sum_sq`（オーバーフロー）、`effect_leak`（エフェクト漏れ） |

## 不変条件と、それを守る検査

| 不変条件 | 検査 |
|---|---|
| Wisp 往復: 任意の正規形 `f` で `wisp::parse(&wisp::print_all(&f)) == f` | `tests/properties.rs` の `any_canonical_form_roundtrips_through_wisp_and_pretty`、`tests/m0.rs`、`wisp.rs` のテスト。新しい構文には往復テストを足す |
| 出力はすべて S式。エラーは `(error :kind K :msg "..." ...)`。数値キーは単位付き（`-ms`）。usage だけは stderr | `tests/cli.rs` の `every_error_kind_prints_one_sexp_and_exits_with_its_class`。ライブラリは `src/lib.rs` で `print_stdout` を禁じる |
| 終了コード: 0 成功 / 1 実行時・契約・エフェクト・型 / 2 構文・ロード・使い方 / 3 性能予算超過 / 101 内部エラー | `diag::ErrorKind::exit_code` と `tests/cli.rs` の `exit_class` |
| i64 はラップしない。溢れたら `overflow` エラー | `tests/cli.rs` の overflow の例、`tests/runtime_diff.rs` |
| エフェクト検査は推移的 | `tests/m0.rs` の `effect_leak_is_caught_transitively`、`effects.rs` のテスト |

## コマンド

`nix develop` で CI と同じ Rust 1.99.0（`rust-toolchain.toml`）と z3 5.1.0、JDK、elan、perf、inferno が入る。変更の確認は `scripts/verify`（`docs/verification.md`）。

```
cargo build --release
cargo test --release              # 深い再帰があるので release 推奨
cargo clippy --release --all-targets -- -D warnings   # CI と同じ
target/release/warrant run   examples/msort.wrt --report
target/release/warrant check examples/msort.wrt            # z3 が PATH にあれば契約を証明する
target/release/warrant fmt   examples/msort.wrt            # → Wisp 表示
target/release/warrant bench examples/msort.wrt -n 10      # 既定は --contracts auto
target/release/warrant spec-diff OLD.wrt NEW.wrt           # 仕様の弱体化があれば終了コード 1
scripts/bench-compare.sh main                              # main と交互に bench を取り、退行なら終了コード 1
scripts/flamegraph.sh examples/msort.wrt out.svg           # perf と inferno が必要
scripts/profile-breakdown.sh examples/msort.wrt out.svg    # 同。コピー・解放・割り当て・解釈の割合を S式で出す
scripts/bench-sizes.sh "1000 2000 4000 8000" 3            # gen の引数を変えて msort を測る（O(n²) の確認）
formal/tla/check.sh                                        # TLC で仕様を検査（jar は検証して取得）
formal/lean/check.sh                                       # Lean の証明をビルドし、sorry がないことを確かめる
```

## 変更の手順

- 新しい組み込み関数: `builtin.rs` の `Builtin` に足し、`rt.rs` の `builtin()` に実装し、`tests/runtime_diff.rs` に例を足して期待値を書き直し（`bless_golden`）、型エラー・境界エラーを S式で返す。コンパイラが match の漏れを指す箇所（型検査、VC 生成など）もすべて埋める
- 新しい節 `(:xxx ...)`: `ast.rs` の `Lowerer::clause` に足し、`check` の出力と DESIGN.md の言語の節を更新する
- 新しい失敗の種類: `diag::ErrorKind` に足し、`exit_code` で分類を決め、`tests/cli.rs` の `exit_class` にも足す
