# ベンチマーク記録

`target/release/warrant bench examples/msort.wrt -n 10` の median を記録する。
環境: x86_64, 24 論理コア, Linux 6.8, rustc 1.94 nightly, release ビルド。各条件 3 回測り、median の中央値を載せる。

| 日付 | コミット | 条件 | median (ms) | 備考 |
|---|---|---|---|---|
| 2026-11-19 | M0 取り込み | 契約あり（runtime） | 151.8 | 3 回: 151.4 / 152.0 / 151.8 |
| 2026-11-19 | M0 取り込み | 契約なし（`--no-contracts`） | 55.5 | 3 回: 55.4 / 55.5 / 55.8 |

M0 の DESIGN.md にある値（231 / 87 ms）とは別のマシンの値。比較は同じ表の中だけで行う。
