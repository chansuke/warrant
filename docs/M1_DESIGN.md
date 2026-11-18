# M1 設計: 静的検証

最終更新: 2026-11-19（M1 着手時点）

M1 では、型・エフェクト・契約を実行前に検査し、証明できた契約は実行時検査を省く。
この文書は、データの形、モジュールの分担、SMT への符号化、作業の順序を決める。
確定した判断は `docs/DESIGN.md` の Decision Log（D13 以降）に1行ずつ書く。

## 1. データの形

すべての静的検査は、位置付きの AST（`ast::Module`）を入力にする。
S式（`Sexp`）は保存と表示の形式のままにして、位置を持たせない。

```
ソース ─parse─▶ Vec<Sexp> ＋ Vec<SpanTree> ─lower─▶ ast::Module
                    │                                  │
                    └─▶ eval::Program（インタプリタ）    ├─▶ types::check   → TypeInfo
                                                       ├─▶ effects::check → EffectInfo
                                                       ├─▶ vc::generate   → Vec<Obligation>
                                                       └─▶ specdiff::diff
```

### 1.1 位置（M1-1）

```rust
pub struct Pos { pub line: u32, pub col: u32 }
/// Sexp と同じ形の木。葉にも節にも開始位置を持つ。
pub struct SpanTree { pub at: Pos, pub kids: Vec<SpanTree> }
```

- `sexp::parse_all_spanned(src) -> (Vec<Sexp>, Vec<SpanTree>)` と `wisp::parse_spanned` を足す。既存の `parse_all` / `wisp::parse` は木を捨てるだけの薄い関数にする
- Wisp の行から作ったリストの位置は、その行の先頭の要素の位置。`:` で作ったリストは `:` の次の要素の位置
- `Sexp` の等価性は変わらないので、往復テストはそのまま成り立つ
- `SpanTree` を読むのは `ast::lower` だけ。他のパスは `Expr.at` を使う

### 1.2 AST

```rust
pub struct Module { pub fns: Vec<FnDecl> }             // ソース順。名前引きは index で
pub struct FnDecl {
    pub name: String, pub at: Pos,
    pub params: Vec<Param>,                           // Param { name, ty: Type, at }
    pub ret: Type,
    pub spec: Spec,
    pub body: Vec<Expr>,
    pub source: Sexp,                                 // 正規形。キャッシュ、spec-diff、インタプリタが使う
}
pub struct Spec {
    pub effects: Option<EffectSet>,                   // None = 宣言なし（推論結果を表示するだけ）
    pub requires: Vec<Clause>, pub ensures: Vec<Clause>,
    pub budget: Option<Budget>,
}
pub struct Clause { pub expr: Expr, pub index: usize }
pub struct Expr { pub id: ExprId, pub at: Pos, pub kind: ExprKind }
pub enum ExprKind {
    Int(i64), Bool(bool), Str(String),
    Local(String), Global(FnIdx), Builtin(Builtin),   // 名前解決は lower で済ませる
    VecLit(Vec<Expr>),
    If(Box<[Expr; 3]>), Let(Vec<(String, Expr)>, Vec<Expr>),
    Lambda(Vec<Param0>, Vec<Expr>),                   // Param0 { name, ty: Option<Type> }
    Do(Vec<Expr>), And(Vec<Expr>), Or(Vec<Expr>),
    Call(Box<Expr>, Vec<Expr>),
}
pub enum Type { I64, Bool, Str, Vec(Box<Type>), Fn(Vec<Type>, Box<Type>, EffectSet) }
```

- 名前解決（局所変数・トップレベル関数・組み込み）を `lower` で1回だけ行う。未定義シンボルは `lower` のエラー（`:kind unbound :at ...`）になる
- `defn` の引数と戻り値の型注釈は必須。注釈のない `defn` は `lower` で `:kind syntax` のエラー
- `Expr.id` は型検査の結果（`TypeInfo: Vec<Type>`、id で引く）を VC 生成に渡すための鍵

### 1.3 組み込み関数の表

いまは名前の配列 `BUILTINS` と `builtin()` の `match` が対応を持っている。
M1 では型・エフェクト・SMT の符号化も組み込みごとに要るので、`enum Builtin` と1つの表にまとめる。

```rust
pub enum Builtin { Add, Sub, Mul, Div, Mod, Eq, Lt, Le, Gt, Ge, Not, Len, Get, Slice, Rest,
                   Concat, Cons, IsEmpty, Range, Vec, Map, Fold, Filter, IsSorted, IsPerm, Print }
pub struct BuiltinSpec { pub name: &'static str, pub sig: Sig, pub effects: &'static [Effect] }
pub enum Sig { Fixed(&'static [TyPat], TyPat), Variadic { min: usize, arg: TyPat, ret: TyPat } }
```

`TyPat` は `I64 | Bool | Str | Vec(a) | Fn(..) | Var(n)` で、使うたびに新しい型変数で実体化する。
インタプリタは当面 `name` で引く。表を正とし、`BUILTINS` はこの表から作る。

## 2. パスの分担

| パス | 入力 → 出力 | 失敗の kind |
|---|---|---|
| `ast::lower` | `Sexp` ＋ `SpanTree` → `Module` | `syntax` `unbound` |
| `types::check` | `Module` → `TypeInfo` | `type` `arity` |
| `effects::check` | `Module` ＋ `TypeInfo` → 関数ごとの推論結果 | `effect` |
| `vc::generate` | `Module` ＋ `TypeInfo` → `Vec<Obligation>` | — |
| `solver::Z3` | SMT-LIB テキスト → `Outcome` | `solver`（Z3 が無い、異常終了） |
| `cache` | `Obligation` → 前回の `Outcome` | — |
| `specdiff::diff` | `Module` 2つ → 節の差分 | — |

各パスは純粋関数で、エラーは `Vec<Diag>` で返す。`Diag` の S式化は1か所（`diag.rs`）にまとめる。
`main.rs` は呼び出しと終了コードの決定だけを持つ。

### 2.1 型検査（M1-2）

- 関数の中だけで単一化する単相の推論（Hindley–Milner から let 多相を除いたもの）。型変数は関数ごとに作り、関数の外へは出さない
- 組み込みの多相（`get : (Vec a) i64 -> a` など）は使う箇所ごとに実体化する
- `=` は同じ型の値どうしに限り、関数型は拒否する
- 関数の終わりに解けなかった型変数（例: どこにも使われない `[]`）は `(Vec i64)` に既定化せず、型エラーにする

### 2.2 エフェクト検査（M1-3）

- 呼び出しグラフの不動点で、関数ごとのエフェクト集合を推論する
- 関数値は「潜在エフェクト」を持つ。ラムダは本体のエフェクト、名前付き関数は推論結果、組み込みは表の値
- `map` / `fold` / `filter` のエフェクトは、渡した関数の潜在エフェクト
- 関数型の引数を呼ぶと、その引数の型注釈にある潜在エフェクトが起きる（§6 の Q1）
- 宣言 `(:effects [...])` が推論結果を含まなければ `(error :kind effect :at ... :fn F :declared [...] :inferred [...] :via (log print))`

### 2.3 VC 生成（M1-4）

本体を記号実行し、パス条件の下で守るべき性質を1つずつ `Obligation` にする。

```rust
pub struct Obligation {
    pub fn_name: String, pub kind: VcKind, pub at: Pos,
    pub script: String,                 // 前置き＋宣言＋仮定＋(assert (not goal)) の完結した SMT-LIB
    pub inputs: Vec<(String, Type)>,    // 反例として値を取り出す変数
}
pub enum VcKind { Requires { callee: String, index: usize }, Ensures { index: usize },
                  Overflow, DivZero, Bounds, Unsupported { what: String } }
```

- 1つの VC が1つの完結したスクリプトになる。ハッシュしてキャッシュでき、並列にも投げられる
- 関数ごとのモジュラー検証。呼び出しは、呼ばれる側の `requires` を VC にし、`ensures` を仮定にする（再帰も同じ）
- 契約の式そのものの境界・オーバーフローも VC にする（契約は全域で定義されている必要がある）
- 符号化できない式（`perm?`、入れ子のベクタなど）を含む節は `Unsupported` とし、実行時検査に残す。仮定する側では黙って捨てる（仮定を減らすだけなので健全）

## 3. SMT への符号化

### 3.1 整数

- i64 は SMT の `Int`。引数、呼び出し結果、ベクタの要素には「i64 の範囲内」を仮定し、算術の結果には「範囲内」を VC にする（D13）
- `mod` は `rem_euclid` で、SMT の `mod` と同じ意味になる
- `/` は 0 方向への切り捨てで、SMT の `div`（ユークリッド除算）とは負数で異なる。`(ite (>= a 0) (div a |b|) (- (div (- a) |b|)))` に `b` の符号を掛けて表す。オーバーフローは `i64::MIN / -1` のときだけ

### 3.2 ベクタ（プロトタイプで決めた）

```smt2
(declare-datatypes () ((VI (mk-vi (arr (Array Int Int)) (len Int)))))
(define-fun sorted ((v VI)) Bool
  (forall ((i Int) (j Int)) (! (=> (and (<= 0 i) (<= i j) (< j (len v))) (<= (select (arr v) i) (select (arr v) j)))
                              :pattern ((select (arr v) i) (select (arr v) j)))))
```

- `rest` `cons` `slice` `concat` `range` は `lambda` で配列を作る
- `sorted?` は隣り合う要素の比較ではなく全ペアの比較で定義する（実行時の意味は同じ。量化子のトリガーが効きやすい）
- 要素型ごとにデータ型を作る（`VI` は i64、`VB` は Bool、`VS` は Str）。入れ子のベクタは M1 では `Unsupported`

プロトタイプの結果（`z3 5.1.0`、merge の「a と b が空でなく `a[0] <= b[0]`」の分岐）:

| 表現 | 再帰呼び出しの requires | 結果の sorted? |
|---|---|---|
| `Seq Int` ＋ 隣接比較 | unknown（2 秒で打ち切り） | unknown |
| `(Array Int Int, len)` ＋ 全ペア比較 | unsat（proved） | unsat（proved）、全体で 0.016 秒 |

結果の sorted? を示すには、呼び出し先の `ensures` に「結果の先頭は `a` か `b` の先頭」という節が要る。
M1-4 で `merge` の `:ensures` に次の節を足す（仕様の強化なので M1-7 のガードは弱体化と見なさない）。

```
(or (empty? result)
    (and (not (empty? a)) (= (get result 0) (get a 0)))
    (and (not (empty? b)) (= (get result 0) (get b 0))))
```

### 3.3 関数値

- `map f v` は、`f` がラムダか名前付き関数なら `(mk (lambda ((i Int)) f(v[i])) (len v))` にする。`f` の本体の VC は「`0 <= i < len v` のすべての `i` について」の形で出す
- `filter` と `fold` の結果は新しい定数にし、型の範囲だけを仮定する。`fold` に渡した関数の VC は「アキュムレータと要素が任意の i64 のとき」の形で出す。だから `(fold + 0 ...)` のオーバーフローは常に証明できない
- 範囲を制限した正しい `sum-sq` は、`fold` ではなく再帰で書いた例題にする（§6 の Q2）

### 3.4 反例

ソルバが `sat` を返したら、同じプロセスに `(get-value ...)` を送って `inputs` の値を読む。
ベクタは `len` を読み、先頭から最大 8 要素を読む。出力は S式で、例えば

```
(vc :fn sum-sq :kind overflow :at (line 7 col 22) :status failed :counterexample (xs [0 4000000000]))
```

## 4. ソルバとキャッシュ

```rust
pub trait Solver { fn version(&self) -> &str; fn check(&mut self, ob: &Obligation, timeout_ms: u64) -> Outcome; }
pub enum Outcome { Proved, Failed { model: Vec<(String, String)> }, Unknown { reason: String } }
```

- `Z3Process` は `z3 -in -t:<ms>` を起動し、標準入力にスクリプトを書く。クレートは足さない（D14）
- キャッシュは VC 単位。キーは `ハッシュ(ソルバのバージョン ＋ スクリプト)`。値のファイルにスクリプトの全文も入れ、読むときに一致を確かめる。ハッシュの衝突で誤って proved を返すことがない（D15）
- スクリプトには呼び出し先の契約だけが入り、本体は入らない。だから関数 F の本体を変えると F の VC だけが変わり、F の契約を変えると F とその呼び出し元の VC が変わる
- 置き場所は `.warrant/cache/`。`.gitignore` 済み

## 5. 実行時検査の省略（M1-6）

```rust
pub enum ContractMode { Runtime, Auto, Off }
pub struct ContractPlan { pub requires: Vec<bool>, pub ensures: Vec<bool> }   // true = 実行時に検査する
```

- `ensures[i]` は、その関数の `Ensures { index: i }` の VC が proved なら検査しない
- `requires[i]` は、プログラム中のすべての呼び出し箇所の `Requires { callee, index: i }` が proved なら検査しない。関数を値として渡した箇所（`(map f xs)`）は呼び出し箇所が見えないので、その関数の `requires` はすべて検査に残す
- 停止性は仮定する（`:termination assumed`）。証明は部分正当性の意味で、これを `check` に明記する
- インタプリタは M1 では `Sexp` を評価したままにする（D16）。`--contracts auto` と `runtime` の差が契約検査だけになり、計測が比べやすい

## 6. 実装前に確認する言語の意味論

HANDOFF_M1 の制約に従い、次の3点は実装前にユーザーに確認する。

- **Q1 関数型の構文と潜在エフェクト**。推奨は `(Fn [i64] i64)` を純粋、`(Fn [i64] i64 :effects [io])` を io ありとする書き方。引数に渡す関数の潜在エフェクトは、引数の型注釈に含まれていなければならない
- **Q2 仕様で全要素を語る手段**。推奨は実行もできる組み込み `(all? pred xs)` を足すこと。SMT では `0 <= i < len` の全称量化になる。範囲を制限した `sum-sq` の `:requires` に使う
- **Q3 `=` の型**。推奨は同じ型の値どうしだけを許し、関数どうしの比較を型エラーにすること。M0 の実行時は関数どうしなら常に false を返していた

## 7. 作業の順序

各行が1コミット。各コミットで `cargo test --release` と `cargo clippy --release` を通す。

| # | 作業 | 検査 |
|---|---|---|
| 1 | 設計文書、BENCH.md のベースライン | — |
| 2 | M1-1 `SpanTree`、`parse_all_spanned`、`wisp::parse_spanned` | 位置の単体テスト（`.wrt` と `.wisp`） |
| 3 | M1-1 `ast::lower`、`Builtin` の表、`eval::load` を `Module` から作る形に置き換え、ロードエラーに `:at` | 既存テスト ＋ `:at` のテスト |
| 4 | M1-2 `types::check`、`check` の `(types ...)`、`run`/`bench` の前段と `--no-typecheck` | 型エラー5種類のテスト、例題3つが通る |
| 5 | M1-3 `effects::check` | `effect_leak.wrt` を `check` で検出 |
| 6 | M1-4 `Solver`、`Z3Process`、整数と境界の VC、反例 | `sum_sq.wrt` が反例付きで失敗 |
| 7 | M1-4 呼び出し・契約・ベクタの VC、`sum_sq_ok.wrt`、merge の `ensures` の強化 | merge / msort の VC が proved |
| 8 | M1-5 キャッシュと `check` の `(smt ...)` 集計 | 2回目の `check` がキャッシュヒット、本体を変えた関数だけ再証明 |
| 9 | M1-6 `--contracts auto|runtime|off`、関数ごとのレベル | BENCH.md に3条件、auto が runtime より速い |
| 10 | M1-7 `spec-diff` | 弱体化の各パターンのテスト |

## 7.1 検討して採らなかった案

- **`Sexp` に位置を持たせる**: 往復テストの等価性が位置で壊れるので、比較から位置を除く `PartialEq` を手書きすることになる。全パスが `Sexp` を直接読む形も残り、名前解決や節の解析が各パスに散る
- **ベクタを `Seq Int` で表す**: §3.2 のとおり、量化子を含む sorted? で Z3 が止まる
- **関数単位のキャッシュ（正規形＋呼び出し先の契約をハッシュ）**: VC のスクリプトをハッシュすれば、同じ情報が自動で含まれ、キーの作り方を別に保守しなくてよい
- **M1 でインタプリタを AST の評価に移す**: 速くなるが、M1-6 の計測に契約以外の差が混ざる。M2 で独自ランタイムに置き換えるので、そこでまとめて行う
