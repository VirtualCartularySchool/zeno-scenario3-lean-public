# アキレスと亀：シナリオ 3 の Lean 4 による形式化（第 3.1 版とクラインの壺型閉包）

次の二つの文書に対応する Lean 4 の形式化である。二つの文書は、Zenodo の別の記録として公開する（DOI：<https://doi.org/10.5281/zenodo.24216078>）。このリポジトリのファイルの写しは、Zenodo のソフトウェアの記録として保存する（DOI：<https://doi.org/10.5281/zenodo.24216372>）。

1. 論文「アキレスと亀の追いつき点の理想化と、表裏・前後の正則な反転：ガブリエル・ホーン対の上の構成と Lean 4 による形式化」（第 3.1 版）。
2. 研究用の証明本文「Zeno シナリオ 3 — クラインの壺型閉包（形式証明と原構想の接続）」（2026 年 11 月 14 日、段階 6）。

*Lean 4 formalization accompanying (1) the paper "Idealizing the catch-up point of Achilles and the tortoise: regular reversal of side and order on a pair of Gabriel's horns, with a Lean 4 formalization" (version 3.1), and (2) the research proof text "Zeno Scenario 3 — the Klein-bottle closure: formal proofs and their connection to the original conception" (14 November 2026, stage 6). The two documents are published as a separate Zenodo record (DOI: <https://doi.org/10.5281/zenodo.24216078>). A copy of the files of this repository is archived as a Zenodo software record (DOI: <https://doi.org/10.5281/zenodo.24216372>).*

これは、外部の独立した学術査読を経ていない研究の記録である（プレプリントに対応するソース）。作成には生成 AI を実質的に用いた。Lean の検査が保証する範囲は、下の「Lean の検査が保証すること」に述べる。

*This is a research record that has not been externally peer reviewed; generative AI was used heavily in its preparation. What the Lean check does and does not guarantee is stated below.*

## 主な宣言

### 論文（第 3.1 版）

| 宣言 | 内容 | ファイル |
|---|---|---|
| `Zeno.MainTheorem`、`Zeno.mathemagical_main` | 主定理（論文の定理 1.1） | ZenoSmale/Main.lean |
| `Zeno.M2Theorem`、`Zeno.mathemagical_m2` | 定理 M2：射影平面の上の内在的な表裏の交換（論文の定理 1.2） | ZenoSmale/M2.lean |
| `Zeno.mathemagical_complete` | 定理 1.1 と定理 1.2 を合わせたもの | ZenoSmale/M2.lean |
| `Zeno.Model.two_sided_no_exchange` | 両側の面では M2 は起きない（定理 11.2） | Zeno/MobiusRun.lean |
| `Zeno.Smale.mob_plane`、`Zeno.Model.mobS_isMobius` | 射影平面のはめ込み（定理 11.6） | ZenoSmale/Mobius.lean、Zeno/MobiusRun.lean |
| `Zeno.Model.mobius_passage` | 射影平面の上の走者（定理 11.7） | Zeno/MobiusPassage.lean |
| `Zeno.regular_headline`、`Zeno.regular_headline_outside` | 【議論】の形（系 10.3、系 10.4） | ZenoSmale/Main.lean |
| `Zeno.Model.zeno_steps_force_coincidence` | ゼノンの一致の強制（定理 10.1） | Zeno/Meaning.lean |
| `Zeno.Model.regular_tendstoUniformly_T` ほか 8 定理 | 正則な形から理想形への一様収束（定理 6.5 と定理 8.9 の (vi)） | Zeno/Uniform.lean |
| `Zeno.mathemagical_nonvacuous` | 具体的な競走での主定理 | ZenoSmale/Main.lean |

論文の番号との対応は PAPER_LEAN_MAP.md にある。

### クラインの壺型閉包（証明本文）

| 宣言 | 内容 | ファイル |
|---|---|---|
| `Zeno.mathemagical_klein_closure`（束 `Zeno.Smale.KleinClosure`） | 定理 K（クラインの壺型閉包）の全項 | ZenoSmale/KleinClosure.lean |
| `Zeno.mathemagical_klein_static`、`Zeno.mathemagical_klein`、`Zeno.mathemagical_klein_synthesis`、`Zeno.mathemagical_klein_conception` | 定理 K の入れ子の束（静的な面、動く面の上の走者、同じ F の上の全効果、原構想への橋） | Zeno/KleinMain.lean、ZenoSmale/KleinMain.lean、ZenoSmale/KleinSynthesis.lean、ZenoSmale/KleinConception.lean |
| `Zeno.Smale.neck_eversion` | 首の裏返しの存在（定理 4.1。相対的な h 原理による） | ZenoSmale/KleinEversion.lean |
| `Zeno.Smale.FM_regularHomotopy`、`Zeno.Smale.kleinM_closed_surface` | 滑らかな商曲面 M と、正則ホモトピーの降下（§2） | ZenoSmale/KleinSmooth.lean |
| `Zeno.Smale.klein_argument_form` | 【議論】の形（系 K） | ZenoSmale/KleinConception.lean |
| `Zeno.Smale.no_uniform_dynamic_passage_pos`、`Zeno.Smale.dynamic_stages_bounded` | 量化の順序（定理 7.1） | ZenoSmale/KleinStages.lean |
| `Zeno.Smale.formed_meeting_iff`、`Zeno.Smale.common_parameter_iff`、`Zeno.Smale.static_collision_iff` | D7：形成後の方程式、共通の複素助変数の形の判定条件、衝突の判定条件（定理 6.A、定理 6.J、定理 6.F） | ZenoSmale/KleinDoors.lean、ZenoSmale/KleinReadings.lean |
| `Zeno.Smale.klein_rotor_crossing`、`Zeno.Smale.rotor_real_solution_iff`、`Zeno.Smale.catchup_module_iff` | D7：回転子を未知数に加えた出会いの方程式（静的な面の上の、主定理の導線での解。回転子が実数の解があることと、位置の一致の同値）。実ベクトル空間の上の一次方程式の、指定した元 e についての解 τ = t∗·e（定理 6.K、定理 6.L） | ZenoSmale/KleinRotor.lean |

証明本文の各定理には、対応する Lean の名前を挙げてある。

宣言の名前は、その宣言の文が述べること以上のことを意味しない。`Zeno.mathemagical_complete` は、論文の定理 1.1 と定理 1.2 を合わせた宣言の名前であり、研究の計画の全体の完成を意味しない。`Zeno.Smale.klein_rotor_crossing` の crossing は、構想の記録の「交叉」と同じものであることを主張しない。

## 依存

Lean v4.35.0（lean-toolchain）、Mathlib v4.35.0（56a005855ea17e0b0958f73ec801ae140b0a1679）、sphere-eversion（33ab3d626854a0f0f04ed5772e3102d652e96475）。版は lake-manifest.json で固定してある。

## 再現

```
sha256sum -c SHA256SUMS.txt
lake exe cache get
lake build
lake env lean Audit.lean > AXIOMS_INDEPENDENT.txt
diff -u AXIOMS.txt AXIOMS_INDEPENDENT.txt
```

SHA256SUMS.txt は、このリポジトリの、SHA256SUMS.txt 自身を除くすべてのファイルを列挙する（検証用のワークフローを含む）。

Audit.lean は二つの検査を行う。第一に、主要な 369 の宣言のおのおのについて `#print axioms` を実行する。第二に、モジュール Zeno.* と ZenoSmale.* のすべての宣言から依存をたどり、現れる公理の和集合を一行で出力する。AXIOMS.txt はその出力であり、どの宣言も `propext`、`Classical.choice`、`Quot.sound` だけに依存する。

.github/workflows/independent-lean.yml は、GitHub Actions の上で、SHA-256 の照合、build（Mathlib は build 済みのキャッシュを取得し、sphere-eversion とこのリポジトリのモジュールはソースから build する）、公理の出力の比較、証明の穴と危険な宣言の検索を行う。

再現できると述べるのは、このリポジトリのソースからの Lean の build と、上の検査である。文書の PDF を組み立てる道具は、このリポジトリに含まれない。

## Lean の検査が保証すること

Lean のカーネルが保証するのは、Lean の定義から Lean の定理文が導かれることである。その定義と定理文が文書の数学を正しく表していることは、論文の付録 A、付録 B と PAPER_LEAN_MAP.md、および証明本文の記法と各定理の対応による読み合わせで確かめる。Lean の検査は、構想の記録との意味の上の対応や、研究の完成を保証するものではない。文書の自然言語による説明と、Lean の定理の文が食い違う場合には、Lean の定理の文が、検査された正確な主張である。証明本文は、Lean の定理、本文で証明した命題、引用、解釈、確立していない命題を区別して述べている。

## 生成 AI の利用

Lean のソースは、生成 AI（Anthropic 社の Claude）が作成した。検証用のワークフローは OpenAI 社の ChatGPT が作成した。詳しくは論文の「生成 AI の利用についての宣言」による。文書と形式化は、著者の研究体制の中で、生成 AI による内部検討・点検を受け、その指摘に基づく局所訂正を反映した。これは、外部の独立した学術査読ではない。検討の主体の数は、独立した証拠の数ではない。

## ライセンス

Apache License 2.0（LICENSE）。依存するライブラリは、それぞれのライセンスに従う。

## この記録について

これは固定した研究の記録である。保守、個別の質問への回答、訂正や追加の証明の依頼への対応は行わない。
