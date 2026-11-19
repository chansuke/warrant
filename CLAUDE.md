# CLAUDE.md — Warrant

AIエージェント向けの検証付き並列言語 Warrant の処理系（Rust）。
設計判断は `docs/DESIGN.md`、次の作業は `docs/HANDOFF_M1.md` を読むこと。

## コマンド

```
cargo build --release
cargo test --release              # 深い再帰があるので release 推奨
cargo clippy --release            # 警告ゼロを維持
target/release/warrant run   examples/msort.wrt --report
target/release/warrant check examples/msort.wrt
target/release/warrant fmt   examples/msort.wrt            # → Wisp 表示
target/release/warrant bench examples/msort.wrt -n 10
```

## コード構成

| ファイル | 役割 |
|---|---|
| `src/sexp.rs` | 字句解析・構文解析（位置付きエラー、`SpanTree`）、`flat` / `pretty` 表示、`is_clause` |
| `src/wisp.rs` | Wisp 表示の印字と構文解析（可逆、`parse_spanned`） |
| `src/ast.rs` | `lower`: defn と節の解析、名前解決、型注釈の解析。静的検査はすべてここの `Module` を読む |
| `src/builtin.rs` | 組み込み関数の `enum Builtin` と名前の対応 |
| `src/diag.rs` | 静的検査のエラー `Diag`（`:at` 付きの S式） |
| `src/eval.rs` | `Program::new`（`Module` から作る）、`Interp`（評価、契約、エフェクト、組み込み関数） |
| `src/profile.rs` | `Profiler` と `report`（S式出力） |
| `src/main.rs` | CLI。大きいスタックのスレッドで実行し、終了コードを返す |
| `tests/m0.rs` | 例題の往復・実行・エラー種別の統合テスト |
| `examples/` | `msort`（目標プログラム）、`sum_sq`（オーバーフロー）、`effect_leak`（エフェクト漏れ） |

## 守るべき不変条件

1. **Wisp 往復**: 任意の正規形 `f` で `wisp::parse(&wisp::print_all(&f)) == f`。印字規則を変えたら `tests/m0.rs` と `wisp.rs` のテストを通す。新しい構文を足したら往復テストも足す
2. **出力はすべて S式**。エラーは `(error :kind K :msg "..." ...)`。数値キーは単位付き（`-ms`）。人間向けの文章を stdout に混ぜない（usage だけは stderr）
3. **終了コード**: 0 成功 / 1 実行時・契約・エフェクト違反 / 2 構文・ロード・使い方 / 3 性能予算超過。新しい失敗の種類は既存の分類に入れる
4. **i64 はラップしない**。算術は checked で、溢れたら `overflow` エラー
5. エフェクト検査は推移的（呼び出しスタック上のすべての宣言を見る）
6. 依存クレートは理由があるときだけ追加し、`docs/DESIGN.md` の Decision Log に1行書く

## 作業の進め方

- 小さく分けてコミットする。各コミットで `cargo test --release` と `cargo clippy` が通る状態にする
- 性能に関わる変更は、前後で `warrant bench examples/msort.wrt -n 10` を取り、コミットメッセージに median を書く
- 設計判断を変える・新しく決めるときは `docs/DESIGN.md` の Decision Log に追記する（番号 D13 から）
- 新しい組み込み関数: `builtin.rs` の `Builtin` に足し、`eval.rs` の `builtin()` に実装し、型エラー・境界エラーを S式で返す。コンパイラが match の漏れを指す箇所（型検査、VC 生成など）もすべて埋める
- 新しい節 `(:xxx ...)`: `ast.rs` の `Lowerer::clause` に足し、`check` の出力と DESIGN.md の言語の節を更新する
