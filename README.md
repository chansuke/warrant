# Warrant (M0)

AIエージェントが実装を書き、人間は**仕様（法）だけ**を承認する言語。
コードは「仕様を満たす根拠（warrant）」が揃ったときだけマージされる。

- 設計判断と背景: [`docs/DESIGN.md`](docs/DESIGN.md)
- 次の作業（M1）の引き継ぎ: [`docs/HANDOFF_M1.md`](docs/HANDOFF_M1.md)
- 開発ルール: [`CLAUDE.md`](CLAUDE.md)

## 設計の柱

| 柱 | 方針 |
|---|---|
| 構文 | 正規形は S式（`.wrt`）。人間向けには Wisp 風のインデント表示（`.wisp`）を可逆変換で提供 |
| 検証 | Dafny / F* 型の SMT 自動証明 ＋ 段階的検証（unspecified → runtime-checked → proved） |
| 速さ | 実行速度より「検査・証明・コンパイル」の速さを優先。ハッシュ単位の証明キャッシュ |
| 安全 | エフェクト型（推移的に検査）。純粋と証明された関数は自動並列化の対象 |
| ループ | 出力もエラーもすべて S式。性能予算 `(:budget ...)` を仕様に書き、超過はマージ不可 |
| 実装 | 処理系もランタイムも Rust。ホットパスは C ABI 境界で Zig/C に差し替え可能 |

## 仕様と実装の分離

```
(defn msort [xs : (Vec i64)] -> (Vec i64)
  (:effects [])                              ; ← 仕様（人間 or 上位エージェントが承認）
  (:ensures (sorted? result) (perm? result xs))
  (let [n (len xs)] ...))                    ; ← 実装（AI が書く）
```

節（clause）は `(:keyword ...)` の形で自己区切りになっていて、機械的に差分を取れる。
M1 以降、節の変更は別権限とし、`ensures` の削除・弱体化（仕様のすり抜け）を検出して止める。

## CLI

```
warrant run   FILE [--report] [--no-contracts]
warrant check FILE
warrant fmt   FILE [--to wisp|sexp]
warrant bench FILE [-n N] [--no-contracts]
```

終了コード: `0` 成功 / `1` 実行時・契約・エフェクト違反 / `2` 構文・ロード / `3` 性能予算超過

### 出力例（`run --report`）

```
(result [2 3 12 13 21 22 31 32 41 42])
(report
  (status ok)
  (check (parse-ms 0.052) (types :status skipped :until M1) (smt :status skipped :until M1))
  (run (wall-ms 309.264) (contracts runtime)
       (calls 25588) (closure-calls 2000) (builtin-calls 296013) (max-depth 2002)
       (vec-allocs 64764) (vec-elems 10028809) (contract-checks 94346) (contract-ms 175.677))
  (hot
    (msort :calls 3999 :incl-ms 308.330 :pct 99.7)
    (merge :calls 21587 :incl-ms 298.454 :pct 96.5)))
```

エラーも S式: `(error :kind effect :msg "..." :trace (log add main))`

## Wisp ビューの規則

- `head a b` + インデントした子行 = `(head a b 子1 子2 ...)`
- 要素1つだけで子のない行はその要素そのもの（`xs` はシンボル、`(f)` は1要素リスト）
- 単独の `:` は行末までを入れ子にする: `fold + 0 : map f xs` = `(fold + 0 (map f xs))`
- `. a b` は親に要素を展開（包まない）
- `( )` `[ ]` の中は通常の S式。括弧は同じ行で閉じる。インデントはスペースのみ

## M0 の範囲

- [x] S式パーサ（位置付きエラー）、正規形プリティプリンタ
- [x] Wisp ビュー（双方向・可逆。テストで往復を保証）
- [x] 参照インタプリタ（i64 はオーバーフロー検査、ラップしない）
- [x] 契約の実行時検査（`:requires` / `:ensures`、`result` 束縛）
- [x] エフェクトの推移的な動的検査（`print` = `io`）
- [x] プロファイラ（関数別の包括時間、確保量、契約コスト）とベンチ（性能予算）

## ロードマップ

- **M1**: 型・エフェクト検査を静的に／`:ensures` から VC 生成 → Z3／定義ハッシュによる証明キャッシュ／仕様差分の権限分離
- **M2**: 独自ランタイム（Perceus 風 RC ＋ work-stealing fork-join）／純粋関数の自動並列化／1コア対 Nコアの並列効率をレポート
- **M3**: 人間が仕様だけを書き、エージェントがマージソートを実装 → 証明 → ベンチ → マージまでループを完結

## M0 で既に見えていること

`msort` の実行時間のうち約 57% が契約検査（`contract-ms`）で、ベクタのコピーは約 1000 万要素ある。
つまり、

1. 契約を M1 で**静的に証明して実行時検査を消す**だけで 2〜3 倍速くなる
2. `cons` / `rest` によるコピーは、M2 の RC ＋ 一意参照時のインプレース更新で消せる

というのが、ループの最初の改善目標になる。
