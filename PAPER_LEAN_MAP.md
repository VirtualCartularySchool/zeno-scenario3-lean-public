# 論文と Lean の対応

論文「アキレスと亀の追いつき点の理想化と、表裏・前後の正則な反転：ガブリエル・ホーン対の上の構成と Lean 4 による形式化」（第 3.1 版）の番号と、このリポジトリの Lean の名前の対応である。以下の各節は、論文の §12.2、付録 A、§12.4、§12.5 をそのまま写したものである。節の番号（§、定理、補題など）は論文の番号である。クラインの壺型閉包の証明本文については、本文の各定理に Lean の名前を挙げてあり、主な宣言は README.md にある。

## 主定理と定理 M2 の欄（論文 §12.2）

主定理は、競走 R ごとの命題の構造体 `Zeno.MainTheorem R` であり、その欄が定理 1.1 の各部分にあたる（全文は付録 B）。

| 欄 | 本文 |
|---|---|
| `ideal` | 定理 4.1 |
| `meridian` | 命題 3.4 |
| `charts` | 命題 5.1 |
| `neck` | 命題 6.3 |
| `regular` | 定理 6.5 の (i)–(v) と岸の条件 |
| `regular_limit` | 定理 6.5 の (vi) の各時刻の収束 |
| `tube`、`tube_keeps`、`no_equivariant`、`symmetric_neck` | 定理 7.1 |
| `umbrella_ends`、`umbrella` | 定理 8.2 |
| `plane_horn`、`plane_immersion` | 補題 8.1 |
| `flex` | 定理 8.5、系 8.6、定理 8.9（(vi) は各時刻の収束） |
| `complex_form` | §8.4 の複素表示 |
| `smale` | 定理 9.1 |

定理 `Zeno.mathemagical_main (R : Race) : MainTheorem R` がすべての欄を証明する。定理 6.5 と定理 8.9 の (vi) の一様な評価と一様収束は、主定理の構造体の外の定理 `regular_uniform_T`、`regular_uniform_A`、`regular_tendstoUniformly_T`、`regular_tendstoUniformly_A`、`flex_uniform_T`、`flex_uniform_A`、`flex_tendstoUniformlyOn_T`、`flex_tendstoUniformlyOn_A` として述べる（主定理の文は変えていない）。`flex` の欄の存在命題は、h 原理によって実際に証明されており、仮定ではない。系 10.3 と系 10.4 は `Zeno.regular_headline` と `Zeno.regular_headline_outside`、定理 10.1 は `Zeno.Model.zeno_steps_force_coincidence` である。`Zeno.mathemagical_nonvacuous` は、d₀ = 1、vₜ = 1、vₐ = 2（r = ½、t∗ = 1）の具体的な競走について、主定理と系 10.3 の形を具体的な数値で述べたものである。

定理 1.2 は、競走 R ごとの命題の構造体 `Zeno.M2Theorem R` であり、定理 `Zeno.mathemagical_m2 (R : Race) : M2Theorem R` がそのすべての欄を証明する（全文は付録 B.10）。

| 欄 | 本文 |
|---|---|
| `obstruction` | 定理 11.2 |
| `fold` | 命題 11.3 の 2、3 |
| `core_model` | 命題 11.4 |
| `projective` | 定理 11.6（`IsMobPlane` と面 S の条件 `IsMobiusSurface`）、定理 11.7（`MobiusPassage`） |

`Zeno.mathemagical_complete (R : Race) : MainTheorem R ∧ M2Theorem R` は定理 1.1 と定理 1.2 の連言であり、二つの面を一つのはめ込みに同定する定理ではない。`MainTheorem` の文と `mathemagical_main` の証明は第 2.1 版から変えておらず、第 3 版で加えたのは新しいファイルと、ライブラリの根のファイルと Audit.lean への行の追加だけである。

## 本文と Lean の対応（論文 付録 A）

Lean の名前は、注記のないかぎり名前空間 `Zeno.Model` の中にある。「欄」は構造体の欄（その構造体の定理が証明する個々の主張）を指す。

| 本文 | Lean | 種類 |
|---|---|---|
| 定理 1.1 | `Zeno.mathemagical_main`、`Zeno.MainTheorem` | 定理 |
| 競走、ゼノンの段階 | `Race`、`Race.g`、`Race.tn`、`Race.A_succ_eq_T`、`Race.tendsto_tn` | 定義、定理 |
| 補題 2.2 | `IdealPassage` の欄 `formation_A`、`formation_T`、`formation_P`、`formation_step`。`continuous_invOP` | 欄、定理 |
| 命題 2.3 | `two_doors`、`inv_right_left`。`IdealPassage` の欄 `door`、`door_limits`、`door_forced`、`door_not_zero` | 定理、欄 |
| 命題 3.1 の 1 | `dot_N_N`、`N_ne_zero` | 定理 |
| 命題 3.1 の 2 | `dot_N_Tv`、`dot_N_Tw`、`IdealPassage.orientation`、`IdealPassage.tangents` | 定理、欄 |
| 命題 3.1 の 3 | `IdealPassage.collapse` | 欄 |
| 命題 3.1 の 4 | `inv3_G_eq_H`、`xhat_G`、`IdealPassage.chart`、`IdealPassage.horn_pair` | 定理、欄 |
| 命題 3.1 の 5 | `IdealPassage.mirror_sym` | 欄 |
| 命題 3.1 の 6 | `IdealPassage.symmetric`、`IdealPassage.frame_law` | 欄 |
| 命題 3.1 の 7 | `IdealPassage.surface_level`、`IdealPassage.criterion` | 欄 |
| 命題 3.1 の 8 | `gradPhi_G`、`dot_gradPhi_N`、`side_G_N` | 定理 |
| 命題 3.1 の 9 | `gradPhi_neg`、`side_neg_pos` | 定理 |
| 定義 3.2 | `side`、`Front`、`Back`、`Everse` | 定義 |
| 命題 3.3 | `hasDerivAt_Phi_line`、`eventually_pos_of_hasDerivAt`、`front_outside`、`back_inside`。Ψ については `hasDerivAt_Psi_line`、`Psi_Pch` | 定理 |
| 命題 3.4 | `MainTheorem` の欄 `meridian`（`lemniscate`、`meridian_formula`、`meridian_velocity`） | 欄 |
| 補題 3.5、系 3.6 | `rigid_normal`、`side_mul_of_rigid`。面の場合は `normal_rigid`、余向きの場合は `coorientation_rigid` | 定理 |
| 法線場、余向き | `IsNormalField`、`IsCoorientation` | 定義 |
| θ（θ(0) = 0） | `theta` | 定義 |
| 定理 4.1 | `ideal_passage : IdealPassage R` | 定理 |
| 定理 4.1 の (ii) | `IdealPassage` の欄 `twist_step`、`twist_count`、`twist_escape`、`twist_angle`、`twist_image`、`twist_normal`、`step_compact`。`theta_pow`、`no_angle_limit`、`normal_no_limit`、`continuous_stepPoint`、`injective_stepPoint` | 欄、定理 |
| 定理 4.1 の (iii) | 欄 `meet_before`、`meet_after`、`meet_discrete`。`meetings_eq`、`meetings_infinite`、`meetings_finite_off_wp` | 欄、定理 |
| 定理 4.1 の (iv) | 欄 `coorientation`、`rigid`、`frame_law`、`side_T_before`、`side_T_after`、`side_A_before`、`side_A_after` | 欄 |
| 定理 4.1 の (v) | 欄 `order_xhat`、`order_before`、`order_after`、`door`、`follow_before`、`follow_after` | 欄 |
| 定理 4.1 の (vi) | 欄 `nearer`、`coincide` | 欄 |
| 定理 4.1 の (vii) | 欄 `horn_volume`、`horn_area`、`dictionary_time`、`dictionary_area`、`dictionary_thin`、`dictionary_fat`。定義 `hornV`（Vol）、`hornA`（Ar） | 欄、定義 |
| 命題 5.1 | `chart_dichotomy : ChartDichotomy`（欄 `projective_keeps` など）。射影チャートの基準は `Psi`、`gradPsi`、`sideP` | 定理、定義 |
| 命題 5.2 | `Zeno.Smale.framePt_neg`（多様体の場合）、`FamilyFacts` の欄 `frame_law`（平面の場合） | 定理、欄 |
| 補題 6.1 | `neck_lemma`、`cross_sig`、`neck_core` | 定理 |
| §6.2 の定義 | `cut`、`hh`（h）、`rho`（ρ）、`kap`（β）、`psi`（ψ）、`AA`（𝔞）、`BB`（𝔟）、`Sig`（Σ）、`Xf`（Ñ）、`rot2`（Rot₂） | 定義 |
| 補題 6.2 | `AA_sq_add`、`BB_pos`、`radial_eq`、`radial_ne`、`profile_ne` | 定理 |
| 命題 6.3 | `Sig_isNeckSurface : IsNeckSurface w₀ (Sig w₀) (Xf w₀)` | 定理 |
| §6.3 の定義 | `ell`（ℓ）、`thetaSm`（θ̃）、`VtR`（Vₜ）、`VaR`（Vₐ）、`Race.runT`、`Race.runA` | 定義 |
| 定理 6.5 | `regular_passage : RegularPassage …` | 定理 |
| 定理 6.5 の (i) | 欄 `reversal`、`side_T_right`、`side_T_left`、`side_A_right`、`side_A_left`。岸の条件は `MainTheorem` の欄 `regular` | 欄 |
| 定理 6.5 の (ii) | 欄 `agree_T`、`agree_A`、`smooth_T`、`smooth_A` | 欄 |
| 定理 6.5 の (iii) | 欄 `step_before`、`step_after` | 欄 |
| 定理 6.5 の (iv) | 欄 `nearer`、`antipodal`、`no_collision`、`min_dist`、`thick` | 欄 |
| 定理 6.5 の (v) | 欄 `compare_before`、`compare_after`、`compare_zero`、`compare_not_collision`、`approach_T`、`approach_A`、`recede_T`、`recede_A`、`follow_before`、`follow_after` | 欄 |
| 定理 6.5 の (vi) | 一様な評価は `regular_uniform_T`、`regular_uniform_A`、一様収束は `regular_tendstoUniformly_T`、`regular_tendstoUniformly_A`（Zeno/Uniform.lean）。各時刻の収束は `regular_tendsto_T`、`regular_tendsto_A` | 定理 |
| 定理 7.1 の 1 | `Tub`（𝒯）、`XT`、`Tub_isTubeSurface : IsTubeSurface w₀ (Tub w₀) (XT w₀)` | 定義、定理 |
| 定理 7.1 の 2 | `tube_no_reversal` | 定理 |
| 定理 7.1 の 3 | `no_equivariant_neck` | 定理 |
| 定理 7.1 の 4 | `symmetric_neck_passes_wp` | 定理 |
| §8.1 の定義 | `tau`（τ）、`chiC`（χ）、`qC`（λ）、`planeG`（γ）、`SS`（S）、`n0`（n₀）、`WW`（W）、`Lam`（Λ） | 定義 |
| 補題 8.1 | `planeG_polar`、`n0_polar`、`cross_D1_D2`、`WW_pos`、`planeG_immersion`、`nsq_planeG_le`、`nsq_planeG_le_half` | 定理 |
| 定理 8.2 | `umbrella_crease`、`Lam_zero`、`Lam_pi` | 定理 |
| §8.2 の定義 | `nh`（ν）、`Rod`、`sig`（σ）、`kapS`（κ）、`phiS`（φ）、`chiT`（χ̃）、`bsP`（B）、`LL`（L）、`blendM` | 定義 |
| 補題 8.3 | `frame_inj`、`LL_inj`、`blend_core` | 定理 |
| 補題 8.4 | `hol_identity` | 定理 |
| 定理 8.5 | `Zeno.Smale.plane_eversion_rel_horn`、`IsPlaneEversion`。使う h 原理は sphere-eversion の `immersionRel_satisfiesHPrincipleWith` と `RelMfld.SatisfiesHPrincipleWith.bs` | 定理、定義 |
| 系 8.6 | `family_facts : FamilyFacts κ₀ ε f`。法線場は `XF`（𝒩）、族の法線場は `IsFamilyNormal` | 定理、定義 |
| §8.4 の定義 | `Race.sT`、`Race.rhoT`、`Race.thT`、`Race.yTt`、`Race.yAt`、`Race.zT`、`GG`（𝔾）、`zOf` | 定義 |
| 複素表示 | `GG_real`、`GG_polar`、`zOf_eq` | 定理 |
| 定理 8.9 | `flex_passage : FlexPassage …`。比較の核は `xhat_kLam`、`xhat_diff`、`order_numerator_pos`、非衝突の核は `bb_lt`、`zetaSq_kLam` | 定理 |
| 定理 8.9 の (vi) | 一様な評価は `flex_uniform_T`、`flex_uniform_A`、一様収束は `flex_tendstoUniformlyOn_T`、`flex_tendstoUniformlyOn_A`（Zeno/Uniform.lean）。各時刻の収束は `flex_tendsto_T`、`flex_tendsto_A` | 定理 |
| 定理 9.1 | `Zeno.SmaleFacts`、`Zeno.smale_facts`（`Zeno.Smale.exists_isEversion`、`Zeno.Smale.smale_endpoints`、`Zeno.Smale.not_immersion_const`、`Zeno.Smale.sphere_eversion_close`、`Zeno.Smale.eversion_in_ball`） | 定理 |
| 定理 10.1 | `zeno_steps_force_coincidence` | 定理 |
| 系 10.2 | `ideal_continuousAt`、`ideal_coincidence_forced` | 定理 |
| 系 10.3 | `Zeno.regular_headline` | 定理 |
| 系 10.4 | `Zeno.regular_headline_outside` | 定理 |
| 具体例（§12.2） | `Zeno.mathemagical_nonvacuous` | 定理 |
| 単位法線をもつはめ込みの裏返し（§12.1） | `Zeno.Smale.surface_eversion`（主定理には入らない） | 定理 |
| 定理 1.2 | `Zeno.mathemagical_m2`、`Zeno.M2Theorem`。定理 1.1 と合わせた形は `Zeno.mathemagical_complete` | 定理 |
| 定理 11.2 | `two_sided_no_exchange`、`M2Theorem` の欄 `obstruction` | 定理、欄 |
| 命題 11.3 | `Ypp`、`Ypp_deck`、`exists_Ypp`、`G_mirror`、`foldG`、`foldG_of_pos`、`foldG_of_neg`、`foldG_deck`、`planeG_Ypp`、`M2Theorem` の欄 `fold` | 定義、定理、欄 |
| 命題 11.4 | `mobC`、`mobCw`、`mobCv`、`mobC_deck`、`mobC_periodic`、`mobC_cross_ne`、`contDiff_mobC`、`mobC_zero`、`M2Theorem` の欄 `core_model`。座標 y では `mobCy`、`mobCy_Ypp`、`mobCy_chain` | 定義、定理、欄 |
| §11.3 の定義 | `MobOK`、`mT0`（T₀）、`mDl`（Δ）、`stg`、`sgA`、`sgB`、`sgC`、`A0`、`Bm`（B）、`rotX`、`rotZ`、`rotA`、`fr`（F）、`wY`、`frY`、`LY`、`Lfull`（L）、`bsM`（bs） | 定義 |
| 補題 11.5 の 1 | `fr_horn`、`fr_core`、`A0_eq_zero`、`shape_disc`、`shape_inj`、`fr_inj`、`LY_eq_planeG`、`Lfull_inj` | 定理 |
| 補題 11.5 の 2 | `LY_dYw`、`LY_dYv`、`LY_eq_mobCy`、`bsM_eq_planeG`、`bsM_eq_mobCy`、`bsM_holonomic` | 定理 |
| 定理 11.6 の前半 | `Zeno.Smale.mob_plane`、`IsMobPlane`。形式解は `Zeno.Smale.mobSol`、固定する閉集合は `Zeno.Smale.mobFixed`、ホロノミーは `Zeno.Smale.mobSol_hol_near` | 定理、定義 |
| 定理 11.6 の後半 | `mobS`（S）、`mobX`（X）、`IsMobiusSurface`、`mobS_isMobius`。一つの側は `IsMobiusSurface.no_side`、モノドロミーは `IsMobiusSurface.monodromy` | 定義、定理 |
| §11.4 の定義 | `Race.mc`（c）、`Race.mkc`（k）、`Race.mδ`（δ）、`Race.mw`（w₀）、`Race.mε`（ε）、`Race.mok`、`ellM`（ℓ）、`VAM`（Vₐ）、`VTM`（Vₜ） | 定義、定理 |
| 定理 11.7 | `mobius_passage : MobiusPassage R n₁ S X`、`M2Theorem` の欄 `projective` | 定理、欄 |
| 定理 11.7 の (i) | 欄 `reversal`、`side_T_right`、`side_T_left`、`side_A_right`、`side_A_left`。核は `IsMobiusSurface.X_right`、`IsMobiusSurface.X_left`、`IsMobiusSurface.front_right`、`IsMobiusSurface.back_left`、`IsMobiusSurface.reversal`、`cross_mirror`、`side_mirror` | 欄、定理 |
| 定理 11.7 の (ii) | 欄 `one_sided`、`no_side`、`monodromy` | 欄 |
| 定理 11.7 の (iii) | 欄 `exchange_T`、`exchange_A` | 欄 |
| 定理 11.7 の (iv) | 欄 `agree_T`、`agree_A`、`smooth_T`、`smooth_A` | 欄 |
| 定理 11.7 の (v) | 欄 `step_before`、`step_after` | 欄 |
| 定理 11.7 の (vi) | 欄 `at_infinity` | 欄 |
| 定理 11.7 の (vii) | 欄 `no_collision`、`min_dist`、`thick`。核は `mob_sep`（`sep_core_core`、`sep_core_mid`、`sep_core_horn`、`sep_mid_horn_q3`、`sep_mid_horn_q1`） | 欄、定理 |
| 定理 11.7 の (viii) | 欄 `compare_before`、`compare_after`、`compare_zero`、`follow_before`、`follow_after` | 欄 |
| 定理 11.7 の (ix) | 欄 `uniform_T`、`uniform_A`。核は `mob_window` | 欄、定理 |
| 系 11.8 | 定理 11.7 の欄と `IsMobiusSurface.monodromy` の組み合わせで、別の定理にはしていない | 注記 |

## 設計上の注意（論文 §12.4）

1. **結論の欄**：結論は命題の構造体（理想形、首の上の走者、動く面の上の走者、裏返しの族の性質、チャートの二分、球面、主定理）にまとめ、各欄を一つの定理として述べた。表裏のラベルは、面と走者の定義に現れず、常に Φ と法線から計算される。
2. **一点コンパクト化**：ℝ ∪ {∞} は Mathlib の `OnePoint ℝ` である。X = 1/w は `invOP` で、その連続性が `continuous_invOP` である。
3. **勾配**：∇Φ は多項式の式 `gradPhi` で定義し、それが方向微分であることを `hasDerivAt_Phi_line` で証明した。命題 3.3 は `front_outside` と `back_inside` である。
4. **ℝ³ の扱い**：Zeno では ℝ³ を ℝ × ℝ × ℝ とし、|q|² を内積で定める。この積空間の距離は最大値ノルムなので、定理 8.5 の近さは ‖ ‖∞ で述べた。ZenoSmale の球面の部分は sphere-eversion のユークリッド空間 ℝ³ を使う。
5. **階段関数**：s₀ は `Real.smoothTransition` である。
6. **体積と面積**：Vol と Ar は区間積分で定義した。
7. **θ(0) の規約**：θ は `Real.log` で定義され、`Real.log` は 0 で 0 をとるので、θ(0) = 0 である（§4）。θ(rw) = θ(w) + 2π は w ≠ 0 の仮定のもとで述べる（`twist_step`、`theta_mul`）。
8. **ι と x̂ の値**：`inv3`（ι）と `xhat`（x̂）は ℝ³ 全体の上で定義され、q = 0 では Lean の除法の規約により 0 をとる。本文はこれらを q ≠ 0 でだけ使い、`criterion` と `xhat_G` もそれぞれ q ≠ 0 と w ≠ 0 を仮定する。
9. **管の仮定**：定理 7.1 の 2 は、`IsTubeSurface` を満たす面について形式化した。`IsTubeSurface` は、法線 ∂F/∂v × ∂F/∂w が連続で消えないことを欄として含む。これは F が滑らかなはめ込みであることから従う。
10. **射影平面の扱い**：α̂ = α ∪ ℓ∞ を一つの型として定義せず、平面の上の写像 f と円柱 ℝ × ℝ の上の写像 S（v について周期 2π、τ で不変）の組で扱う（§11.2）。面の条件は構造体 `IsMobiusSurface` にまとめ、走者の定理 `mobius_passage` はこの構造体だけから証明する。定理 11.6 の後半は `mobS_isMobius` である。
11. **M2 の h 原理**：§11 では解の族は要らないが、ライブラリの定理は媒介変数つきの形なので、P = ℝ を形だけの媒介変数として使い、得られた族の p = 0 の成分を取る（`Zeno.Smale.mob_plane`）。

## 形式化していないこと（論文 §12.5）

次のものは、Lean の定理の文に含めていない。また、定理の文の中で「したがって」「特に」として述べる Lean の文の直接の読み替え（命題 3.1 の 2 と 3 の、はめ込みであるかどうか、補題 8.1 の 3 の γ(y) → ℘、系 8.6 の 4 の後半など）も、Lean の文そのものではない。

- 注意 8.8 の回転の向きについての観察（数値計算による）。
- 注意 3.7 で、M2 が起きないことの議論。閉じた道についての定理 11.2 は形式化した（`two_sided_no_exchange`）。定理 1.1 の三つの形への適用（定理 11.2 の直後の段落）は、その定理と各形の法線場の連続性からの一行の帰結であり、独立の定理にはしていない。
- 命題 11.3 の 1 の、y が τ による商の上で単射であること。Lean は τ 不変性（`Ypp_deck`）と全射性（`exists_Ypp`）を証明する。円柱の商がメビウスの帯であること、α̂ が射影平面であることは、空間を型として定義していないので、同一視の記述である。
- 系 11.8 の最後の、亀とアキレスの導線に子午線の半周を継ぎ足した閉路。Lean のモノドロミーの定理（`IsMobiusSurface.monodromy`、`MobiusPassage` の欄 `monodromy`）は、終点が始点の τ による像である任意の道について述べており、この特定の二つの道は構成していない。
- 定理 11.7 の (ix) の「したがって」以下の一様収束の極限の文。Lean は一様な評価（欄 `uniform_T`、`uniform_A`）を証明する。
- 注意 11.9 の 3 の、射影平面が埋め込めないことと、一般の位置にあるはめ込みについての Banchoff の定理の引用（文献の事実）、ホーンと芯の模型がそれぞれ単射であること（短い計算で確かめられるが、本稿では証明も形式化もしない）。
- 注意 6.4。命題 6.3 からの直接の帰結であり、独立の定理にはしていない。
- §10.4 の「主張しないこと」。定理ではない。
- 付録 C の構想の記述との対応、注意 8.10 の形の対応。解釈についての指摘であり、定理ではない。
- 命題 3.4 の、(q₁, ρ) 座標での言い換え、双曲線 xy = 1 の反転であること、接線の角と変曲点の記述。Lean は符号つきの等式 (a² + b²)² = ab と C、C′ の式を証明する。言い換えは a と b が同符号であることから、ほかは C′ の式からの短い計算で出る。
- §2 の、差の式 (r − 1)/(rg) の ℝ ∪ {∞} への延長についての注意。Lean は二人の射影座標の道をそれぞれ扱う（定理 4.1 の (v)）。

Lean の定義と本文の定義の対応は、付録 A と付録 B による読み合わせで確かめるものである。
