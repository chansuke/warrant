# Warrant 設計ドキュメント

最終更新: 2026-11-20（M1 完了後、perm? の証明を追加）

## 1. 目的

AIエージェントが主に実装を書き、**人間はボトルネックにならない**言語を作る。
人間はコードをレビューしない。人間（または上位エージェント）が書いて承認するのは
**仕様（法）だけ**で、実装は「仕様を満たす根拠（warrant）」が機械的に揃ったときだけマージされる。
人間の役割は、ループ（仕様 → AI実装 → 検証 → ベンチ → マージ）を設計すること。

対象領域: Bend と同じく、バックエンド処理と並列計算。

## 2. 先行事例と差別化

| | Bend (v2) | Edict | Warrant |
|---|---|---|---|
| 構文 | Python 風 | なし（JSON AST を直接出力） | 正規形 S式 ＋ 人間向け Wisp 表示（可逆） |
| 検証 | 依存型（affine dependent type theory、Lean 風の手書き証明） | 型・エフェクト ＋ Z3 | SMT 自動証明 ＋ 段階的検証 |
| 実行 | HVM 系（interaction nets）、GPU 並列 | WASM サンドボックス | 独自ランタイム（RC ＋ work-stealing） |
| 人間の関与 | LAWS.bend / PROOF.bend | — | 仕様と実装の権限分離、仕様のすり抜け検出 |

- Bend: https://bend-lang.com/
- Edict（**最も近い競合**。型・エフェクト追跡・Z3 検証まで重なる）: npm `edict-lang`、GitHub `Sowiedu/Edict`
- Bosque（Microsoft、推論しやすさのために言語機能を削る方向）も参考になる

差別化の軸: (1) S式と Wisp の二層構文、(2) 独自の並列ランタイム、(3) 仕様と実装の権限分離、(4) 性能予算を仕様に含める。

## 3. 確定した設計判断（Decision Log）

| # | 判断 | 理由 |
|---|---|---|
| D1 | 正規形は S式（`.wrt`）。人間には Wisp 風インデント表示（`.wisp`）を見せ、双方向に可逆変換する | AIは曖昧さのない構文と構造的な差分編集が得意。人間は括弧がつらい。保存形式と表示形式を分ける |
| D2 | 検証は Dafny / F* 型の SMT 自動証明 ＋ 段階的検証 | 依存型の手書き証明は AI の試行錯誤ループに重い。契約 → 実行時検査 → 証明と段階的に上げられるほうが回る |
| D3 | 「爆速」は**型検査・証明・コンパイルの速さ**を最優先 | ループが何百回も回るため。インクリメンタル化と定義ハッシュによる証明キャッシュ |
| D4 | エフェクト型、機械可読エラー、トークン効率の3つをすべて入れる | エフェクトはエージェントの権限管理と安全性、そして自動並列化の判定に直結する |
| D5 | 仕様（節 `(:effects …)` `(:requires …)` `(:ensures …)` `(:budget …)`）と実装（本体）を分離。仕様の変更は別権限 | AI が `ensures` を削る・弱めることで検証を通す「仕様のすり抜け」が、人間を外したときの最大の急所 |
| D6 | 検証レベルを関数ごとに持つ: `unspecified` / `runtime-checked` / `proved`（＋将来 `assumed`） | マージ可否をループ側で機械的に判定できる（例: `assumed` が残っていればマージ不可） |
| D7 | 性能も仕様の一部。`(:budget (wall-ms N))` を超えたらマージ不可（終了コード 3） | ループで性能退行を自動で防ぐ |
| D8 | ランタイムは独自実装。MVP は**正格評価 ＋ Perceus 風参照カウント ＋ work-stealing fork-join**。interaction nets は見送り | プロファイルが読みやすく改善サイクルが速い |
| D9 | 純粋（`(:effects [])`）と検証済みの関数は、コンパイラが自動で並列化してよい | 安全性の仕組みと速さの仕組みを1つで兼ねる |
| D10 | 処理系もランタイムも Rust。ホットパスで詰まったら、その部分だけ Zig か C に書き直す。境界は C ABI | AIの書きやすさ（学習データ量、エラーの誘導）と安定性。Zig は 1.0 前で破壊的変更が多い |
| D11 | 名前は **Warrant**（正当な根拠・保証＝証明がマージの権利）。拡張子 `.wrt`、CLI `warrant` | Edict / Writ / Tenet は既存プロジェクトと衝突 |
| D12 | 出力・エラーはすべて S式。数値キーは単位付き（`wall-ms`, `incl-ms`） | エージェントがスクレイピングなしで解析できる |
| D13 | SMT では i64 を数学的整数 `Int` で表し、算術の結果ごとに範囲の VC を出す。ベクタは `(Array Int T, len)` のデータ型で表し、`sorted?` は全ペアの量化子で定義する | ビットベクタは非線形の乗算で遅い。`Seq Int` では merge の sorted? が unknown、配列表現では 0.016 秒で proved（M1_DESIGN.md §3.2） |
| D14 | ソルバは SMT-LIB2 のテキストを生成して `z3 -in` をサブプロセスで呼ぶ。`trait Solver` で抽象化し、クレートは足さない | ビルドが軽い。cvc5 などに差し替えやすい。テキストをそのままキャッシュのキーにできる |
| D15 | 証明キャッシュは VC 単位。キーはソルバのバージョンとスクリプトのハッシュで、値にスクリプト全文を持たせて一致を確かめる | 呼び出し先の契約は自動でキーに含まれる。ハッシュ衝突で誤って proved を返さない。暗号学的ハッシュのクレートが要らない |
| D16 | 静的検査は位置付き AST（`ast::Module`）を読む。`Sexp` は位置を持たず、位置は構文解析時に作る並行の木 `SpanTree` から `lower` で AST に移す。インタプリタは M1 では `Sexp` を評価したまま | 往復テストの等価性を保つ。名前解決と節の解析を1か所にする。M1-6 の計測に契約以外の差を混ぜない |
| D17 | 関数型は `(Fn [A ...] R)` で純粋、`(Fn [A ...] R :effects [io])` で潜在エフェクトを持つ。関数を渡す引数の型注釈は、渡す関数のエフェクトを含まなければならない | M0 の動的検査（スタック上のすべての宣言を見る）と静的検査の結果を一致させる。2026-11-19 ユーザー確認済み |
| D18 | 組み込み `(all? pred xs)` を足す。仕様で全要素を語るときに使い、SMT では添字の全称量化になる | 実行できるので、証明できなければ実行時検査に戻せる（段階的検証 D6 と整合）。2026-11-19 ユーザー確認済み |
| D19 | `=` は同じ型の値どうしだけを比較でき、関数どうしの比較は型エラー | M0 は関数どうしなら常に false を返していた。意味のない比較を型で拒否する。2026-11-19 ユーザー確認済み |
| D20 | `--no-typecheck` は型検査だけを省略し、静的なエフェクト検査は `run` / `bench` の前に必ず行う | エフェクトは権限と安全性の仕組み（D4）で、型の都合で外せないほうがよい。検査は 0.02 ms 程度で、省略する理由がない |
| D21 | SMT ではベクタの長さを `0 <= len <= 2^59` と仮定する | インタプリタは `isize::MAX` バイトを超えて `Value`（24 バイト）を確保できないので、実際の上限は約 3.8×10^17。長さ2つの和が i64 に収まり、`(+ (len a) (len b))` のオーバーフローを証明できる。上限が実装と矛盾しないことを `eval.rs` のテストで確かめる |
| D22 | spec-diff の精緻化の証明は、古い契約を持ち新しい関数を呼ぶだけの合成関数 `%refines-f` を VC 生成器にかけて行う | 呼び出しの requires の VC が「古い requires ⇒ 新しい requires」、ensures の VC が「古い requires ∧ 新しい ensures ⇒ 古い ensures」になる。SMT の符号化を2つ持たずに済む。節が呼ぶ補助関数は新しい版で解決する（補助関数の契約も変わった場合は近似） |
| D23 | 証明キャッシュの既定の置き場所は `$XDG_CACHE_HOME/warrant/proofs`（無ければ `~/.cache/warrant/proofs`）。プロジェクト内の `.warrant/cache/` は `--cache-dir` で明示したときだけ使う（D15 の置き場所を変更） | キャッシュの proved は実行時検査を外す根拠になる。ソースと一緒に配られたキャッシュを読むと、偽のエントリで契約違反が素通りする（再現テストあり） |
| D25 | `perm?` は出現回数の関数 `cnt-VI` の一致で表す。`concat` `cons` `rest` `slice` `if` とベクタリテラルの項に、`perm?` が必要としたときだけ回数の定義を足す。`slice` は区間の回数 `rcnt-VI` と分割の公理で扱う。回数の公理と定義は、`perm?` を goal に含む VC にだけ入れる | 補題を書かせる仕組み（新しい節と証明義務）より小さく、msort の 39 VC がすべて proved になる。ベクタ上の量化子を含む公理は、無関係な VC で Z3 が反例を作れず unknown になるため分ける。仮定を減らすだけなので健全。`map` `filter` `range` の回数は定義しないので、それらを経る `perm?` は証明できず実行時検査に残る |
| D27 | `run` / `bench` は M2-1 から IR のランタイム（`ir` + `rt`）で実行する。M1 のインタプリタ（`eval.rs`）は差分テスト `tests/runtime_diff.rs` の oracle としてだけ残し、M2-7 で消す（M2_DESIGN.md では既定の切り替えを M2-2 の終わりとしていた） | 差分テストで値・エラーの kind・メッセージ・trace・プロファイラのカウンタが一致し、M1 を既定に残す理由がない。切り替えのフラグを CLI に足さずに済む。M2-2 の計測の基準も IR のランタイムになる |
| D26 | M2 の fork-join のスケジューラは rayon（`rayon::join`）を使う。依存は M2-5 で足す。自前の work-stealing deque は、rayon のオーバーヘッドがプロファイルに出たときに書く | work-stealing の実装と検証を省き、M2 の時間を表現と粒度の調整に使う。D8 の「work-stealing fork-join」と矛盾しない。2026-11-20 ユーザー確認済み |
| D24 | 括弧の入れ子は 1000 段まで。超えたら構文エラー（終了コード 2） | 型検査・VC 生成・評価はどれも木を再帰でたどる。制限がないと 100 万段の入力でスタックが溢れてプロセスごと落ちる |

## 4. 言語（M0 時点）

```
(defn NAME [p1 : T1 p2 : T2] -> RET
  (:effects [io ...])        ; 省略 = M0 では未検査。[] = 純粋
  (:requires EXPR ...)       ; 事前条件
  (:ensures EXPR ...)        ; 事後条件。result が戻り値に束縛される
  (:budget (wall-ms N))      ; main のみ bench で評価
  BODY ...)
```

- 特殊形式: `if`（else 必須）、`let [x e ...]`、`fn [x] ...`、`do`、`and`、`or`
- 値: i64（オーバーフローはエラー。ラップしない）、bool、str、vec、関数
- 組み込み: `+ - * / mod = < <= > >= not len get slice rest concat cons empty? range vec map fold filter all? sorted? perm? print`（`all?` は M1 で追加、D18）
- `print` だけがエフェクト `io` を持つ。エフェクト検査は**推移的**（呼び出し元すべての宣言を確認）
- M1 から、エフェクトは実行前にも検査する。関数ごとに呼び出しグラフの不動点で推論し、宣言がそれを含まなければ `(error :kind effect :at ... :msg "... via (log print)")`。宣言のない関数は `check` に `:effects undeclared :inferred [...]` と出る。静的に呼び出し先が分からない関数値（注釈のないラムダ引数など）は `io` を持つと見なす
- 型は構文として解析するだけで、M0 では検査しない
- M1 から: `defn` の引数と戻り値の型注釈は必須（`ast::lower` が拒否する）。型は `i64` `Bool` `Str` `(Vec T)` `(Fn [T ...] R)` `(Fn [T ...] R :effects [io])`。未定義シンボルは実行前に `:kind unbound :at (line L col C)` で報告する

### Wisp 表示の規則

- `head a b` ＋ インデントした子行 = `(head a b 子1 子2 ...)`
- 要素1つだけで子のない行はその要素そのもの（`xs` はシンボル、`(f)` は1要素リスト）
- 単独の `:` は行末までを入れ子にする: `fold + 0 : map f xs` = `(fold + 0 (map f xs))`
- `. a b` は親に要素を展開する（包まない）
- `( )` `[ ]` の中は通常の S式。括弧は同じ行で閉じる。インデントはスペースのみ
- 不変条件: **任意の正規形 `f` について `wisp::parse(wisp::print_all(f)) == f`**

## 5. CLI と終了コード

```
warrant run   FILE [--report] [--contracts auto|runtime|off] [--no-typecheck]
warrant check FILE
warrant fmt   FILE [--to wisp|sexp]
warrant bench FILE [-n N] [--contracts auto|runtime|off] [--no-typecheck]
warrant spec-diff OLD NEW [--no-smt] [--timeout-ms N]
証明のオプション（check と、--contracts auto の run / bench）: --timeout-ms N --jobs N --cache-dir D --no-cache
```

`0` 成功 / `1` 実行時・契約・エフェクト違反、check 失敗 / `2` 構文・ロード・使い方 / `3` 性能予算超過

`check` は型検査が通れば VC を生成して Z3 で証明する。出力は `(smt :status ok|failed :vcs N :proved P :failed F :unknown U :unsupported X :ms T :issues (...))` で、証明できなかった VC を `(vc :fn F :kind K :at (line L col C) :status failed :counterexample (xs [...]))` の形で列挙する。VC は `--jobs` 個（既定は論理コア数）の z3 を並列に動かして解く。結果は VC ごとにユーザーのキャッシュディレクトリ（既定 `~/.cache/warrant/proofs`、D23）にキャッシュし、`:cached C` と、今回ソルバにかけた関数 `:reproved (...)`、遅い順の3件 `:slowest ((fn kind ms) ...)` を出す。VC が1つでも failed なら終了コード 1。unknown（タイムアウト、既定 2 秒）と unsupported（入れ子のベクタなど）は失敗にしない。z3 が無ければ `(smt :status unavailable ...)`。再帰する関数は `:termination assumed`（停止性は証明しない）

`run` と `bench` の既定は `--contracts auto`。実行前に VC を証明し（キャッシュ経由）、証明できた節は実行時に検査しない。`ensures` の節は、節そのものと節の式の境界・オーバーフローの VC がすべて proved なら省く。`requires` の節は、すべての呼び出し箇所で VC が proved なら省く。値として渡される関数と `main` の `requires` は常に検査する。`--no-contracts` は `--contracts off` と同じ。出力は `(contracts auto :checked 2 :erased 12 :verify-ms 1.3)`。`check` の関数ごとの行は `:level proved|runtime-checked|unspecified :clauses (requires [...] ensures [...])`

`spec-diff` は2つの版を節ごとに比べる（M1-7）。`:ensures` の削除・変更、`:requires` の追加・変更、`:effects` の拡大・削除、`:budget` の緩和・削除、型シグネチャの変更、関数の削除を `:verdict weakened` とし、1つでもあれば終了コード 1。本体だけの変更は `(impl (f :body changed))` に別に出す（エージェントだけでマージしてよい範囲）。z3 があれば、ensures / requires の変更について「古い requires ⇒ 新しい requires」と「古い requires ∧ 新しい ensures ⇒ 古い ensures」を証明し、示せた変更は `refined` として弱体化から外す（`--no-smt` で省略）

`run --report` は実行の内訳を S式で出す。`(hot ...)` は関数ごとの呼び出し回数、`:incl-ms`（外側の呼び出しだけで数えた包含時間）、`:self-ms`（呼び出し先を除いた時間。契約の評価を含む）。`(clauses ...)` は実行時に検査した節ごとの回数と時間で、節の番号は `check` の `:clauses` と同じ。`(builtins ...)` は組み込み関数ごとの呼び出し回数。外からの計測には `scripts/bench-compare.sh`（基準リビジョンと交互に bench を取り median を比べる）と `scripts/flamegraph.sh`（perf と inferno）を使う

`run` と `bench` は実行前に型検査とエフェクト検査を行い、エラーがあれば実行せず終了コード 1 で終わる。`--no-typecheck` で省略できるのは型検査だけで、エフェクト検査は省略できない（D20）。未定義シンボルと型注釈の欠落はロードの段階で拒否され、終了コード 2

エラーの kind: `parse syntax load unbound type arity bounds overflow div-zero contract effect stack io usage`

## 6. M0 のベースライン計測

`examples/msort.wrt`（n=2000、release ビルド、tree-walking インタプリタ）:

| 条件 | median |
|---|---|
| 契約あり（runtime） | 約 231 ms |
| 契約なし | 約 87 ms |

`run --report` では、実行時間の約 57% が契約検査（`contract-ms`）、ベクタのコピーが約 1000 万要素。
→ M1 で契約を証明して実行時検査を消す、M2 で RC ＋ インプレース更新でコピーを消す、が最初の改善目標。

## 7. ロードマップ

- **M0（完了）**: パーサ、Wisp 相互変換、インタプリタ、実行時の契約・エフェクト検査、プロファイラ、ベンチ
- **M1（完了）**: 静的な型・エフェクト検査／VC 生成 → Z3／証明キャッシュ／証明済み契約の実行時検査の削除／仕様差分ガード（設計は `docs/M1_DESIGN.md`、作業の指示は `docs/HANDOFF_M1.md`、計測は `docs/BENCH.md`）
- **M2**: 独自ランタイム（Perceus RC ＋ work-stealing）、純粋関数の自動並列化、並列効率（1コア対Nコア）のレポート（設計は `docs/M2_DESIGN.md`、作業の指示は `docs/HANDOFF_M2.md`）
- **M3**: 人間は仕様だけを書き、エージェントがマージソートを実装 → 証明 → ベンチ → マージまでのループを完結させる

## 8. 形式検証とテスト

- `formal/lean/`: 契約の省略の健全性。`contracts::levels` の3条件（すべての呼び出し箇所で VC が proved、値として使われない、`main` でない）の下で、`requires` の実行時検査を外しても結果・契約違反・無応答が変わらないことを、関数値と値経由の呼び出しを持つ小さな言語のモデルで証明する（`erasure_sound`）。条件を1つ外すと結果が変わる例も載せる。VC は「解けたときの意味」で仮定し、SMT の符号化そのものの正しさは対象外
- `formal/tla/`: 証明キャッシュ（複数プロセスの同時書き込みとハッシュ衝突）と並列 discharge（ロック付きの共有イテレータ）を TLC で検査する。どちらも、仕組みを外したモデル（その場書き込み、ロックなしの取り出し）で不変条件が破れることを負の対照として確かめる
- `tests/soundness.rs`: ランダムな関数で、全 VC が proved なら全契約を検査して実行しても失敗しないことを確かめる差分テスト。SMT の符号化の誤りを捕まえる（割り算をユークリッド除算にした変異、i64 の上限を1ずらした変異で失敗することを確認済み）
- `tests/properties.rs`: ランダムな正規形の Wisp・pretty 往復と、フロントエンドが panic しないこと
- CI（`.github/workflows/ci.yml`）: test と clippy（`-D warnings`）、PR の bench 比較（15% を超える退行で失敗）、プロファイルと flame graph の成果物、TLC、Lean

## 9. 未決事項

- 停止性: `(:decreases ...)` を入れるか、M1 では `assumed` 扱いにするか
- `perm?` は D25 で `concat` `cons` `rest` `slice` を経るものまで証明できる。`map` `filter` を経るものや、帰納法が要る多重集合の性質（補題をエージェントに書かせる仕組み）は未決。誤った `perm?` がリテラルと比べる形だと、Z3 は反例を作れず unknown を返す
- `fold` の結果は不透明（アキュムレータに不変条件を書く手段がない）。`(:invariant ...)` のような節を足すか、再帰で書かせるか
- 型システムの範囲（多相、ユーザー定義型、所有権／一意性を型に出すか）
- 並列化の粒度の決め方（コストモデル、閾値）
