# 引き継ぎプロンプト: Warrant M1

> このファイルの「プロンプト本文」以下を、そのまま Claude Code に渡す。

---

## プロンプト本文

あなたは Warrant という言語処理系（Rust）の開発を引き継ぎます。M0 は完成済みで、今回の仕事は **M1: 静的検証** です。

### 最初にやること

1. `CLAUDE.md`、`docs/DESIGN.md`、`README.md` をすべて読む。特に DESIGN.md の Decision Log（D1〜D12）は確定事項なので、覆す場合は理由を Decision Log に書いてからにする
2. `git init` して、M0 の状態をそのまま最初のコミットにする（`target/` は `.gitignore` 済み）
3. `cargo test --release` と `cargo clippy --release` が通ることを確認する
4. ベースラインを記録する: `target/release/warrant bench examples/msort.wrt -n 10` と `--no-contracts` 付き。結果を `docs/BENCH.md` に表で残す（以後、性能に関わる変更ごとに追記する）
5. `z3` が使えるか確認する（`z3 --version`）。なければインストール方法をユーザーに伝えて、Z3 が不要なタスク（M1-1〜M1-3）から進める

### 背景（なぜこれを作るか）

Warrant では AI が実装を書き、人間は仕様（`(:effects …)` `(:requires …)` `(:ensures …)` `(:budget …)` の節）だけを承認します。コードは「仕様を満たす根拠」が機械的に揃ったときだけマージされます。M0 では契約を実行時に検査するだけでした。M1 の目標は、**契約を実行前に SMT で証明し、証明できたものは実行時検査を消す**ことです。M0 の計測では msort の実行時間の約 57% が契約検査だったので、これがそのまま速度改善にもなります。

### M1 のタスク（この順で進める）

各タスクは、受け入れ条件を満たし、テストを足し、`cargo test` と `clippy` が通った状態でコミットする。

#### M1-1 ソース位置の保持

- 現在の `Sexp` は位置を持たない。型エラーや反例を `(error ... :at (line L col C))` で返せるように、位置を持たせる
- 方針の推奨: `Sexp` 自体は変えず（往復テストの等価性を壊さないため）、構文解析時に**位置の付いた並行の木**（またはノード ID → 位置の表）を作る。別案を選ぶなら Decision Log に書く
- 受け入れ条件: 既存のテストがすべて通る。Wisp から読んだときも元の行・列が出る

#### M1-2 静的な型検査

- 型: `i64`, `Bool`, `Str`, `(Vec T)`, 関数型。`defn` の引数と戻り値の型注釈は必須にし、`let` と `fn` の中は推論する（単相でよい。多相は M1 では不要）
- 組み込み関数ごとに型を定義する（`map`/`fold`/`filter` は関数引数を取る）
- `check` の出力に型エラーを S式で出す。`(types :status ok)` または `(types :status error :errors (...))`
- `run` / `bench` は型検査が通ったときだけ実行する（`--no-typecheck` で回避できるようにしておく）
- 受け入れ条件: 3つの例題が型検査を通る。型エラーの単体テストを最低5種類（引数の数、戻り値、if の分岐の不一致、vec の要素型、未定義シンボル）

#### M1-3 静的なエフェクト検査

- 呼び出しグラフからエフェクトを推論し、宣言 `(:effects [...])` が推論結果を含むかを検査する。クロージャ経由の呼び出しも追う
- `:effects` を省略した関数は推論結果を `check` に表示する（エラーにはしない）
- 受け入れ条件: `examples/effect_leak.wrt` が実行前に `check` で検出される。エラーは `(error :kind effect ... :at ...)`

#### M1-4 検証条件（VC）の生成と Z3

- **ソルバとの接続の推奨**: Rust の z3 クレートではなく、**SMT-LIB2 のテキストを生成して `z3 -in` をサブプロセスで呼ぶ**。理由: ビルドが軽い、cvc5 などに差し替えやすい、生成したテキストをそのままハッシュしてキャッシュに使える。`trait Solver` で抽象化しておく
- **i64 の表現の推奨**: SMT の数学的な `Int` を使い、すべての算術演算に「結果が i64 の範囲に入る」という VC を出す（ビットベクタは非線形の乗算で遅くなりやすいため）。違う判断をするなら Decision Log に書く
- 関数ごとのモジュラー検証: 本体の中の呼び出しは、呼ばれる側の `requires` を VC として出し、`ensures` を仮定として使う（再帰呼び出しも同じ扱い）
- 生成する VC: 呼び出し先の `requires`、自分の `ensures`、算術のオーバーフロー、`/` と `mod` の 0 除算、`get` / `slice` / `rest` の境界
- ベクタは SMT の `Seq Int` で表す。`len` `get` `slice` `concat` `cons` `rest` を Seq の演算に対応させる。`sorted?` は量化子で定義する。`perm?`（多重集合の一致）は M1 では証明できなくてもよく、その場合は実行時検査のまま残す
- 停止性は M1 では証明しない。`check` で再帰関数を `:termination assumed` と表示する
- 反例: 証明に失敗したら Z3 のモデルから反例を S式で返す。例: `(vc :fn sum-sq :kind overflow :at (line 7 col 22) :status failed :counterexample (xs [4000000000]))`
- タイムアウトは VC ごとに設定でき（既定 2 秒）、タイムアウトは `:status unknown`
- 受け入れ条件:
  - `examples/sum_sq.wrt` の `check` がオーバーフローの VC 失敗と反例を出す（実行前に）
  - 範囲を `:requires` で制限した正しい版の sum-sq を例題に足し、それが `proved` になる
  - `merge` と `msort` の境界・オーバーフローの VC が `proved` になる
  - `merge` の `(sorted? result)` は、必要なら `:ensures` を強める（先頭要素についての事後条件を足すなど）ことで `proved` を目指す。届かなければ、何が足りないかを `docs/BENCH.md` ではなく `docs/DESIGN.md` の未決事項に書く

#### M1-5 証明キャッシュ

- キー: 関数の正規形（本体＋節）＋呼び出す関数の契約＋ソルバのバージョンのハッシュ。値: 結果（proved / failed / unknown）と所要時間
- 置き場所: `.warrant/cache/`（`.gitignore` に追加）
- `check` の出力: `(smt :vcs N :proved P :failed F :unknown U :cached C :ms T :slowest ((fn kind ms) ...))`
- 受け入れ条件: 2回目の `check` がキャッシュヒットで大幅に速くなる。本体を1文字変えた関数とその呼び出し元だけが再証明される

#### M1-6 証明済み契約の実行時検査の削除

- `run` / `bench` に `--contracts auto|runtime|off` を追加し、既定を `auto`（証明済みの契約は検査しない、未証明の契約だけ実行時に検査）にする
- `check` の関数ごとのレベルを `proved` / `runtime-checked` / `unspecified` で出す（一部だけ証明済みなら、節ごとに内訳を出す）
- 受け入れ条件: `docs/BENCH.md` に `runtime` / `auto` / `off` の3条件の median を記録する。`auto` が `runtime` より速いこと

#### M1-7 仕様差分ガード

- `warrant spec-diff OLD.wrt NEW.wrt` を追加する。節の変更だけを抽出し、**弱体化**を検出する:
  - `:ensures` の削除・変更 → 弱体化の疑い
  - `:requires` の追加・変更 → 呼び出し側に対する弱体化の疑い
  - `:effects` の拡大 → 弱体化
  - `:budget` の緩和 → 弱体化
- 本体だけの変更は「実装の変更」として別に列挙する（これは AI だけで マージしてよい範囲）
- 終了コード: 弱体化があれば 1
- 発展（余裕があれば）: 変更された節について「新しい ensures ⇒ 古い ensures」を SMT で確かめ、論理的に強くなっただけなら弱体化扱いしない
- 受け入れ条件: 各パターンの単体テスト

### 制約

- CLAUDE.md の不変条件（Wisp 往復、出力はすべて S式、終了コード、i64 はラップしない）を守る
- 既存の CLI の振る舞いを壊さない。オプションの追加はよい
- 依存クレートを足すときは Decision Log に理由を書く
- 迷ったら、推奨案を選んで先に進み、判断を Decision Log に書く。ただし、言語の意味論を変える判断（例: 型注釈の必須範囲、`if` の意味）は、実装する前にユーザーに確認する

### 完了時に報告すること

- 各タスクの状態（完了 / 部分的 / 未着手）と、部分的なものは何が足りないか
- `docs/BENCH.md` の最新の表
- `check examples/msort.wrt` の出力全文
- 追加した Decision Log の項目
- M2（独自ランタイム、自動並列化）に向けて分かったこと
