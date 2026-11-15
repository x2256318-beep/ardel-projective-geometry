# アーデル射影幾何 — Part 253（PAG 2.0）：原始指標の張る空間の上の作用素 T（0 での延長のあと J∘H_N/√N）— 内積 ip に関してユニタリで、A1 の位相を課した線形写像は原始部分で T と同じ値をとる（線形性による）

2026-11-12。PAG257.lean（34 項目、定義 7 個。うち 6 項目は独立照合 A・C の指摘、4 項目は B の指摘を受けて追加）、step276.py（15 項目。うち 4 項目は独立照合の後に追加）。

- **問いの出所。** 著者の選択です（2026-11-12 21:17「推薦で進めてください」）。着手前の文書 `pag2_part253_preregistration.md` の候補 K1 で、残余は計算だけ、小さいノートの水準と明記して進める、という推奨でした。
  - 本来の道のうち「無限素点を含む大域対象」の有限レベルの部分です。重なりの読みは「ねじれた貼り合わせ（U）」と決まっています（著者の決定、17:14）。
  - Part 252 の独立照合 B が指摘した欠け（固有ベクトルの式はあるが、部分空間の上の作用素の文がない）を埋めます。
  - 盲検の問いテストは着手前に済んでいます（同じ文書の §7 の T1：既知の結果の短い帰結。「Hartley 変換＋逆元」の作用素そのものの文献は見つからず）。
- **問い（幾何の言葉で。解釈）。** 切断した円筒の両端を U で貼り合わせます。A1 のもとで、U は原始指標の部分で、明示的な実の核を持つ作用素として書けるか。その部分の外では何が起こるか。
  - U は Lean で定義していません。Lean で扱うのは明示の作用素 T で、U については「A1 の位相を課した任意の線形写像」という仮定の形でだけ現れます（`TopL_eq_of_A1`）。
- **結論（Lean）。** 単数の上の関数 g に (T g)(u) = (H_N g̃)(u⁻¹)/√N とおきます（g̃ は g を 0 で ℤ/N に延ばしたもの、H_N は離散 Hartley 変換）。⟨f, g⟩ = Σ_u conj(f(u))·g(u)（この内積を ip と書きます）。W(χ) = ε(χ)τ(χ)/√N で、ε(χ) は χ が偶なら 1、奇なら −i です（Part 252 の `rootNum`。原始的な χ ではルート数の式、原始的でない χ ではそうではありません）。
  - T は線形写像で、**すべての指標 χ** について T χ = W(χ)χ です（`TopL_charU`）。
  - 指標は直交し（⟨χ, ψ⟩ = φ(N)·[χ = ψ]、`ip_charU`）、一次独立で、単数の上の関数の空間を張ります（`linearIndependent_charU`、`span_charU_eq_top`）。
  - 原始指標が張る空間 V_prim について：
    - T で不変で、T(V_prim) = V_prim です（`TopL_mem_Vprim`、`map_TopL_Vprim`）。
    - V_prim の上で T は等長です：⟨Tf, Tg⟩ = ⟨f, g⟩（`ip_TopL_of_mem_Vprim`）。全射と合わせて、T は V_prim の上で ip に関してユニタリです。これを 1 つの文にしたものが `unitary_Vprim`（V_prim の自己線形同型で、値は T、ip を保つ）です。Mathlib の内積空間にはつないでいません。
    - 原始指標で U χ = W(χ)χ を満たす**任意の**線形写像 U は、V_prim の上で T と同じ値をとります（`TopL_eq_of_A1`）。仮定は `TopL_charU` の原始部分そのもので、結論は線形性だけから出ます（ほぼ同語反復）。
  - 原始的でない指標が張る空間 V_imprim も T で不変です（`TopL_mem_Vimprim`）。V_prim と V_imprim は ip について直交し、空間全体はその直和です（`ip_Vprim_Vimprim`、`Vprim_inf_Vimprim`、`Vprim_sup_Vimprim`、`isCompl_Vprim_Vimprim`）。V_imprim = V_prim^⊥ という形の文は書いていません。`eq_zero_of_ip_self` は非退化（⟨f, f⟩ = 0 ⇒ f = 0）だけで、⟨f, f⟩ ≥ 0 の文はありません。
  - **自明になる法。** N ≡ 2 (mod 4) では原始指標がなく V_prim = 0 で、V_prim についての文は自明に成り立ちます（法 2 では `Vprim_two`）。法 N ≥ 2 では自明な指標が原始的でなく、V_imprim に入ります（`not_isPrimitive_one_of_two_le`、`charU_one_mem_Vimprim`）。
  - 証人：法 3 で V_prim ≠ 0（`Vprim_ne_bot_three`）。法 2 で V_imprim の上の T は等長でない（自明な指標で |W|² = 1/2、`not_isometry_Vimprim_two`）。法 4 で T は自明な指標を 0 に送り、自明な指標は V_imprim に入るので、T は V_imprim の上で単射でない（`TopL_charU_one_four`、`charU_one_mem_Vimprim`）。
  - 素数の法の証人（独立照合 A の指摘で追加）：すべての素数 p で V_imprim の上の T は等長でない（自明な指標の τ = −1、|W|² = 1/p。`gaussSum_one_prime`・`normSq_rootNum_one_prime`・`not_isometry_Vimprim_prime`）。素数 p ≥ 3 で V_prim ≠ 0（`Vprim_ne_bot_prime`）。したがって素数 p ≥ 3 では、同じ法で V_prim の上はユニタリ（`unitary_Vprim`）、V_imprim の上は等長でありません。
  - sorry 0、警告 0。`#print axioms` 34 行はすべて [propext, Classical.choice, Quot.sound]。
- **Lean でない補足（数値・手計算）。**
  - 証人の限界（独立照合 A・B の指摘）：法 3 の原始指標は奇の 2 次指標 1 つだけで W = 1（τ = i√3）なので、法 3 の T↾V_prim は恒等写像です［手計算・数値］。N ∣ 24 ではいつもそうなります（指標がすべて実）［数値］。位相が自明でない最小の法は 5 で（W ≈ 0.8507 ± 0.5257i）［数値、step276 の (12)。1 ≤ N ≤ 100 の 69 個］。恒等でない位相を示す Lean の証人はありません。
  - 問いの「外側」について：Lean の文は T の性質だけで、V_imprim の上の U は `TopL_eq_of_A1` で何も縛られません。A1 の位相を原始的でない指標にも誘導元から入れた U_N を考えると、V_imprim の上では T ≠ U_N です［数値、着手前の `prereg253_check.py` の (K1c)：‖(T − U_N)↾V_imprim‖ の最小 0.5918］。
- **A1 との関係（第 2 の型の注意）。** `TopL_eq_of_A1` は「原始指標で A1 の位相を満たす任意の線形写像 U」についての文で、A1 の読み替えです。
  - 除去テスト：仮定（A1 の位相）を外すと結論が成り立たなくなるのは、V_prim ≠ 0 の法だけです［数値 (5)：N ≢ 2 (mod 4) の 75 個の法で、原始指標の位相を 1 つ変えると一致しない］。N ≡ 2 (mod 4) では結論はどの U でも成り立ちます。テストの内容は線形性から自明です。
  - 原始的な χ で T の固有値 W(χ) がルート数の式になること（`TopL_charU` の原始指標の場合）は、A1 によりません（ガウス和の事実）。
  - したがって、成果は「A1 の位相を、原始部分で明示の実の核 J∘H_N/√N（0 での延長のあと）として書き直した」ことで、「導いた」のではありません（CLAUDE.md §2・§6。A1 は公準のまま）。
- **位置づけ（正直な評価）。** 既知の事実の書き直しです（再導出、確信度：高）。原始指標で |τ(χ)|² = N（Part 12（PAG16）・Part 252）と指標の直交性から出ます。新規候補はありません。
- **Lean にしていないこと。**
  - V_imprim の上のノルムの評価 ‖T↾V_imprim‖ ≤ 1/√2（等号は N ≡ 2 (mod 4)）。原始的でない指標のガウス和の式 τ(χ) = μ(N/f)χ*(N/f)τ(χ*)（Montgomery–Vaughan, Multiplicative Number Theory I の Thm 9.10。着手前の盲検のエージェントが取得した章の PDF による。Mathlib にない）が要ります。数値は step276 の (10)（99/99 で ‖T↾V_imprim‖ < 1、最大 0.7071）。
  - 法 N の貼り合わせ U_N 全体（原始的でない指標に誘導元の位相を入れたもの）の明示の核。着手前の候補 K2 で、着手していません（数値は `prereg253_check.py` の (K2a)〜(K2d)）。
  - Ẑ^× の上への持ち上げ。U_N は法を上げる引き戻しと両立し、T は両立しません［数値 (K2d)］。「極限の U は L²(Ẑ^×) の上にあり、各導手 f の新しい部分の上で T_f に等しい」は、構成（位相を誘導元から取る）からの見込みです［予想・解釈、確信度：中。Lean にしていない］。
  - 「長さが保たれるのはちょうど V_prim の上」（T は正規な縮小で、V_prim は Sz.-Nagy–Foiaș の標準分解のユニタリ部分。独立照合 C の指摘）。V_imprim の上の |W| < 1 が要るので、Lean にはしていません［数値 (14)、100/100］。

## 0. 内容

### 0.0 ハンドシェイク（CLAUDE.md §0）

- (a) 形式化済み：Part 252（PAG256）の単数の上の式 `JH_eq_rootNum_mul_any`、|W| = 1（`normSq_rootNum`）、除去テストの反例。Part 214（PAG218）の単数の上の指標の和 `sum_units_char`。
- (b) 著者の解釈の層：重なりはねじれた貼り合わせ（U）。A1 は解釈の層の公準（内容は Tate の定理）。解像度のパラメータは未決定（N・K・Λ と同一視しない）。
- (c) 未完の大域の問い：Ẑ の上の定理 A、無限素点を含む大域対象、解像度と有効な姿（§1 の命題 3）の定式化、有限レベルの Bost–Connes。

### 0.1 4 点（着手前の文書の K1 から）

1. 幾何の言葉：上の「問い」。
2. 既存分野の言葉への最善の翻訳：有限アーベル群のフーリエ解析（原始指標はフーリエ変換の固有ベクトルで、固有値はガウス和）。Hartley の核 cas(θ) = ((1−i)e^{iθ} + (1+i)e^{−iθ})/2 から、固有値にパリティの重み i^{−a} が付く。
3. 残余：計算だけ（作用素としての書き直し）。
4. 対照群テスト：Hartley の形がルート数を与えるのは、無限素点の単数が ±1 のとき（ℚ と F_3(t)）だけ。F_p(t) では、χ の F_p^× への制限 η が η² = 1 のときちょうど一致（`prereg253_check.py` の (Cc)、2,292/2,292）。不変な形（有限のガウス和 × 無限素点の局所因子）は Tate の局所ルート数の積［既知］。一般化素数では指標とガウス和がなく、文が定義できない。

### 0.2 定義（PAG257.lean）

| 記号 | Lean | 内容 |
|---|---|---|
| g̃ | `extL` | 単数の上の関数を 0 で ℤ/N に延ばす線形写像 |
| J∘H_N/√N | `JHL` | Part 252 の `JH` を線形写像にしたもの |
| T | `TopL` | `JHL ∘ extL`（単数の上の関数から単数の上の関数へ） |
| χ↾G_N | `charU` | 指標を単数の上の関数とみたもの |
| ⟨f, g⟩ | `ip` | Σ_u conj(f(u))·g(u)（第 1 引数で共役線形） |
| V_prim | `Vprim` | 原始指標の `charU` が張る部分空間 |
| V_imprim | `Vimprim` | 原始的でない指標の `charU` が張る部分空間 |

### 0.3 ラベル（CLAUDE.md §7）

| 結果 | ラベル | 根拠 |
|---|---|---|
| T χ = W(χ)χ（すべての指標） | 既知 | Part 252 の式の作用素の形。平行移動と可換な作用素は指標で対角 |
| 指標の直交性・一次独立・張ること | 既知 | 有限アーベル群の指標の標準の事実 |
| V_prim の不変性・全射・等長（ip に関するユニタリ。1 つの文 `unitary_Vprim` を含む） | 再導出 | 原始指標で \|W\| = 1（\|τ\|² = N）と直交性から |
| A1 の位相を課した任意の線形写像が原始部分で T と同じ値をとる | 既知（自明） | 張る集合の上で一致する線形写像（A1 の読み替え、ほぼ同語反復） |
| V_imprim の不変性、直交する直和 | 既知 | 直交性と非退化 |
| 証人（法 2・3・4） | 既知 | Part 252 の証人と反例 |
| 素数の法の証人、法 N ≥ 2 の自明な指標は V_imprim に入る、法 2 で V_prim = 0 | 既知 | 主指標のガウス和 −1、導手 1 |

- 新規候補：なし。CLAUDE.md §3 の 2 候補にも当たりません。

## 1. 検証表

| 主張 | Lean | 数値（step276） | 新規性 |
|---|---|---|---|
| 0 での延長の値、指標の延長は指標 | `extL_apply`・`extL_charU` | — | 既知 |
| すべての指標で T χ = W(χ)χ | `TopL_charU` | (1) | 既知 |
| 内積の性質（スカラー倍・和の展開） | `ip_smul_smul`・`ip_sum_sum`・`ip_sum_right` | — | 既知 |
| 指標の直交性 ⟨χ, ψ⟩ = φ(N)·[χ = ψ] | `ip_charU` | (2) | 既知 |
| V_prim・V_imprim は T で不変 | `TopL_mem_Vprim`・`TopL_mem_Vimprim` | (3)・(6) | 再導出・既知 |
| 原始指標で W(χ) ≠ 0、T(V_prim) = V_prim | `rootNum_ne_zero`・`map_TopL_Vprim` | (3) | 再導出 |
| 原始指標 χ と任意の ψ で ⟨Tχ, Tψ⟩ = ⟨χ, ψ⟩ | `ip_TopL_charU_prim` | (4) | 再導出 |
| V_prim の上で T は等長 | `ip_TopL_of_mem_Vprim` | (4) | 再導出 |
| 原始指標で A1 の位相を満たす任意の線形写像 U は V_prim の上で T と同じ値をとる | `TopL_eq_of_A1` | (5)（除去テストは V_prim ≠ 0 の 75 個の法） | 既知（自明。A1 の読み替え） |
| ⟨V_prim, V_imprim⟩ = 0 | `ip_Vprim_Vimprim` | (7) | 既知 |
| 指標は一次独立で全体を張る、V_prim ⊔ V_imprim = ⊤ | `linearIndependent_charU`・`span_charU_eq_top`・`Vprim_sup_Vimprim` | (8) | 既知 |
| ⟨f, f⟩ = 0 ⇒ f = 0（非退化）、V_prim ⊓ V_imprim = ⊥、直和 | `eq_zero_of_ip_self`・`Vprim_inf_Vimprim`・`isCompl_Vprim_Vimprim` | (8) | 既知 |
| 証人：法 3 で V_prim ≠ 0 | `Vprim_ne_bot_three` | (11) | 既知 |
| 証人：法 2 で V_imprim の上の T は等長でない | `not_isometry_Vimprim_two` | (9)・(10) | 既知 |
| 証人：法 4 で T は自明な指標を 0 に送る（V_imprim の上で単射でない） | `TopL_charU_one_four`・`charU_one_mem_Vimprim` | (9) | 既知 |
| ‖T↾V_imprim‖ < 1（N ≥ 2）、最大 1/√2 | Lean にしていない | (10)（99/99、最大 0.7071） | 既知（MV Thm 9.10） |
| V_prim の上で T は ip に関してユニタリ（自己線形同型で ip を保つ） | `unitary_Vprim` | (3)・(4) | 再導出 |
| 法 N ≥ 2 の自明な指標は原始的でなく V_imprim に入る | `not_isPrimitive_one_of_two_le`・`charU_one_mem_Vimprim` | — | 既知 |
| 法 2 の指標は自明な指標だけ、法 2 で V_prim = 0 | `eq_one_of_two`・`Vprim_two` | (9) | 既知 |
| 素数 p の自明な指標で τ = −1、\|W\|² = 1/p、原始的でない | `gaussSum_one_prime`・`normSq_rootNum_one_prime`・`not_isPrimitive_one_prime` | (15) | 既知 |
| すべての素数 p で V_imprim の上の T は等長でない。p ≥ 3 で V_prim ≠ 0 | `not_isometry_Vimprim_prime`・`Vprim_ne_bot_prime` | (15) | 既知 |
| T↾V_prim が恒等でない最小の法は 5 | Lean にしていない | (12)（69/100 の N で恒等でない） | — |
| dim V_prim = Σ_{d∣N} μ(d)φ(N/d) | Lean にしていない | (13) | 既知 |
| 長さが保たれるのはちょうど V_prim の上 | Lean にしていない | (14) | 既知（Sz.-Nagy–Foiaș のユニタリ部分） |

## 2. 数値照合（step276.py、15 項目すべて合格、1 秒未満。(12)〜(15) は独立照合の後に追加）

| 項目 | 結果 |
|---|---|
| (1) すべての指標で T χ = W(χ)χ | 100/100（1 ≤ N ≤ 100）、最大誤差 1.6×10⁻¹³ |
| (2) 直交性 | 100/100、最大誤差 1.5×10⁻¹² |
| (3) V_prim は不変で T(V_prim) = V_prim | 100/100 |
| (4) V_prim の上の等長（乱数の f, g） | 100/100、最大誤差 4.3×10⁻¹¹ |
| (5) A1 の位相を課した任意の U（V_imprim の上は乱数）は V_prim の上で T に等しい | 100/100。除去テスト（原始指標の位相を 1 つ変える）75/75 で等しくない |
| (6) V_imprim は不変 | 100/100 |
| (7) ⟨V_prim, V_imprim⟩ = 0 | 100/100 |
| (8) dim V_prim + dim V_imprim = φ(N) | 100/100 |
| (9) 退化ケース | N = 1 で T = 恒等（V_prim が全体）、N = 2 で V_prim = 0・T = −1/√2、N = 3・4 で dim V_prim = dim V_imprim = 1、N = 4 で T(自明な指標) = 0 |
| (10) V_imprim の上で T は等長でない | ‖T↾V_imprim‖ < 1 が 99/99（N ≥ 2）、最大 0.7071。\|W(1 mod 2)\|² = 1/2、\|W(1 mod 4)\|² = 0 |
| (11) 非空虚性 | N = 3・4 で dim V_prim = 1 |
| (12) T↾V_prim が恒等でない N | 69 個（1 ≤ N ≤ 100）、最小は N = 5（W = 0.8507 ± 0.5257i）。N ∣ 24 では恒等 |
| (13) dim V_prim = Σ_{d∣N} μ(d)φ(N/d) | 100/100 |
| (14) I − T*T の零空間 = V_prim（長さが保たれるのはちょうど V_prim の上） | 100/100 |
| (15) 素数 p の自明な指標で τ = −1・\|W\|² = 1/p、p ≥ 3 で V_prim ≠ 0 かつ V_imprim の上で等長でない | 素数 25 個（p ≤ 100） |

- 除去テストの 75 は、原始指標がある N（1 ≤ N ≤ 100 のうち N ≢ 2 (mod 4) の 75 個）です。
- 数値の確認は証明ではありません。

## 3. Lean（PAG257.lean）

- import：PAG256 だけ（鎖を保つ）。Part 214（PAG218）の `sum_units_char` は鎖に入っています。Mathlib の追加ビルドなし（使ったモジュールはビルド済み）。
- 主に使った Mathlib の補題：`MulChar.star_apply'`（conj χ(a) = χ⁻¹(a)）、`MulChar.mul_apply`、`inv_mul_eq_one`、`Submodule.span_le`、`Submodule.mem_span_range_iff_exists_fun`、`LinearMap.eqOn_span`、`Submodule.map_le_iff_le_comap`、`Fintype.linearIndependent_iff`、`LinearIndependent.span_eq_top_of_card_eq_finrank`、`DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity`、`Module.finrank_fintype_fun_eq_card`、`Submodule.span_union`、`Complex.mul_conj`。
- 試しのファイルの 4 回目のコンパイルで通過しました（1 回あたり約 3 秒。ほかに、ゴールを表示するだけの実行が 1 回）。直したエラー：
  - `omit [NeZero N] in` を付けた 2 つの定理が、`NeZero N` を引数にとる def（`extL`）を参照していた（section の instance 変数は、使わなくても def の引数に入る）。
  - `open ZMod` のもとで `map_smul` が `ZMod.map_smul` と曖昧だった（`_root_.map_smul` と書いた）。
  - 内積の展開の証明で `refine Finset.sum_congr` が止まった。最初は文の型の問題と見て `ip (N := N)` を足したが、原因は和の順だった（左辺は (u, j, i)、右辺は (i, j, u)。`conv_lhs => enter [2, j]; rw [Finset.sum_comm]` で内側を入れ替えた）。`(N := N)` は害がないので残した。
  - 証人の定理で、`charU 1`・`rootNum 1` の法が決まらず `NeZero ?N` で止まった（`charU (N := 2) 1`、`(1 : DirichletCharacter ℂ 2)` と型を書いた）。
  - Part 252 の `removal_counterexample_four` の連言の数を 2 回数え違えた（4 つ）。
  - 通過の後、直和の 3 項目（`eq_zero_of_ip_self`・`Vprim_inf_Vimprim`・`isCompl_Vprim_Vimprim`）を足し、1 回で通過しました。
- 独立照合 A・C の後の 6 項目（§9）は、試しのファイルの 2 回目で通過しました。1 回目のエラー：部分空間の元の引き算に強制 `(g : (ZMod N)ˣ → ℂ)` が要った。`let L := …` の写像に `LinearEquiv.ofBijective L ⟨hinj, hsurj⟩` と無名構成子を渡すと型が合わなかった（`let` をやめて `TopL.restrict hres` を直接書き、`have hbij : Function.Bijective … := ⟨hinj, hsurj⟩` にした）。
- 独立照合 B の後の 4 項目（§10）は 1 回で通過しました。
- 件数：theorem/lemma 34、定義 7、`#print axioms` 34 行。通算で theorem/lemma 3,400、`#print axioms` 3,701、xlsx 3,427 項目（行 3395〜3428）、検証手順 273。

## 4. 残る問い（本来の道）

- 法 N の U_N 全体の明示の核（着手前の K2）と、Ẑ^× の上への持ち上げ。どちらも計算の細部か既知の枠組みで、主役にしません。
- 解像度のパラメータは未決定のままです（CLAUDE.md §1 の禁止との緊張は記録済み）。

## 5. 文献の確認の記録（検索ログ）

- 着手前の盲検の問いテスト（`prereg253/`）の T1：「既知の結果の短い帰結」。使う式は Montgomery–Vaughan の Thm 9.5・9.10。近い形として Diaz-Vargas–Glebsky–Rubio-Barrios（arXiv:1803.09239、こちらで実在を確認）の Example 4.2（フーリエ変換∘全単射が乗法的指標の基底で 2×2 と 1×1 のブロックに分かれる）。「Hartley 変換＋逆元」の作用素そのものの文献は見つからなかった。検索語は同じ記録の 10 件。
- 独立照合 C（盲検の命名）が挙げた名前のうち、こちらでウェブで実在を確かめたもの：Hartley の cas（Hartley, Proc. IRE 30 (1942) 144）、離散 Hartley 変換（Bracewell, J. Opt. Soc. Am. 73 (1983) 1832–1835）、Rader の素数長 DFT 算法（Rader, Proc. IEEE 56 (1968) 1107–1108。素数長の DFT を乗法群の上の巡回相関に直す）、Sz.-Nagy–Foiaș（–Langer）の縮小作用素の標準分解（ユニタリ部分と完全非ユニタリ部分）。Davenport の章番号（第 9 章）は確かめていません。
- MathSciNet・zbMATH：未実施（このコンテナからは使えない）。
- 見つからなかったことは、存在しないことの証明ではありません。

## 6. 収束アラームの状況（CLAUDE.md §7、Part 253 の後）

- 辞書の未記入の件数：0（Part 253 の名前は辞書 §13 に足した）。
- 文献照合の未実施の連続パート数：0（着手前の盲検の問いテスト）。
- **兆候 4（初等的な部品の組み合わせだけ）：5 パート連続**（Part 249〜253）。Part 253 は、著者が「小さいノートの水準」と知ったうえで選んだものです。
- **第 2 の型（注入→回収）**：`TopL_eq_of_A1` は A1 の読み替えです（上の「A1 との関係」）。導いたとは書きません。
- 兆候 1〜3：出ていません。
- 対照群テスト：§0.1 の 4。ℚ に固有に見える部分は実素点の局所因子（パリティ）だけで、内容は既知です。

## 7. 検知記録：独立照合（2026-11-12）

照合記録は `pag2_part253_independent_audit.md`、依頼文・エージェントの出力そのもの・構築者の予想は `audit253/` にあります。

- **やり方。** 新しいエージェント 3 つ（general-purpose、文脈なし、入力は依頼文に貼った、ツールを使わないよう指示）。終了の通知のツール使用回数はどれも 0 でした。
  - 入力の中立化：PAG256・PAG257 の定義 11 個を Φ1・Φ2・Φ4・Φ5・Ψ1〜Ψ7 に、定理を S1〜S30 に置き換え、docstring と証明を除きました（`audit253/rename.json`）。入れなかった言葉：Hartley、ルート数、境界、貼り合わせ、A1、モノグラフ、PAG、反転、関数等式。
  - A（逆翻訳）と C（盲検の命名）を先に、B（照合）を A の後に立てました。B には、形式文・A の出力・xlsx の主張・ノートの文面を渡しました（主張とノートの解釈の言葉は照合の対象なので、そのまま）。
- **構築者の予想（結果の前に記録）との対応。**
  - A：S13 はほぼ同語反復、N = 2 で空虚、証人の範囲が狭い、の 3 点は当たりました（A は空虚を N ≡ 2 (mod 4) に一般化）。外れ：法 3 の証人では T↾V_prim が恒等であること、「ユニタリ」が単独の文になっていないこと（後者は B の予想の項に書いていた）。
  - C：cas、離散 Hartley 変換、ルート数、零延長、ℓ² 内積、原始部分／非原始部分、Atkin–Lehner の類似（確信度：低）は当たりました。外れ：Rader（1968）の素数長 DFT 算法、Tate の局所関数等式の有限版、Watson 変換の有限版、Sz.-Nagy–Foiaș の標準分解のユニタリ部分。
  - B：U が形式文にないこと（題で）、ユニタリの根拠の 2 点は当たりました。外れ：S13 の付記「A1 を外すと結論は消える」が N ≡ 2 (mod 4) で偽であること、S19 の「正定値性」、S24 の所属の根拠、ラベルの食い違い、ε の未定義、題の 0 での延長の抜け。
- **受けて直したこと。**
  - A・C の後：`unitary_Vprim`（ユニタリを 1 つの文に）、素数の法の証人（`gaussSum_one_prime`・`normSq_rootNum_one_prime`・`not_isPrimitive_one_prime`・`not_isometry_Vimprim_prime`・`Vprim_ne_bot_prime`）。数値 (12)〜(15)。ノートに証人の限界（法 3 と N ∣ 24 で恒等、位相が自明でない最小の法は 5）。
  - B の後：`not_isPrimitive_one_of_two_le`・`charU_one_mem_Vimprim`・`eq_one_of_two`・`Vprim_two` を足しました。
    - 題を「A1 の位相を課した線形写像は原始部分で T と同じ値をとる（線形性による）」に弱め、0 での延長を入れました。
    - S13 の付記を「仮定を外して結論が成り立たなくなるのは V_prim ≠ 0 の法だけ」に限り、除去テストの範囲（N ≢ 2 (mod 4) の 75 個）を書きました。
    - S19 を「非退化」に、「ユニタリ」を「ip に関するユニタリ」に直しました。ε を定義し、ルート数の読みを原始的な χ に限りました。
    - ラベルを揃えました（V_prim のユニタリは再導出、S13 は既知（自明））。
    - 「Lean でない補足（数値・手計算）」の項を分け、証人の限界と問いの「外側」（V_imprim の上で T ≠ U_N、数値）を移しました。極限の U についての文に［予想・解釈、確信度：中］を付けました。
- **第 11 の型（形式文のずれ）。** B の判定では、xlsx の主張は 30 文中 26 文が形式文と一致、4 文（S13・S19・S23・S24）が「主張が強い」でした。4 文とも主張の側を直し、S23・S24 の根拠は Lean に足しました（`Vprim_two`、`charU_one_mem_Vimprim`）。弱い・別物・空虚の判定はありませんでした。
- **第 2 の型（注入→回収）。** A・B・C がそろって S13（`TopL_eq_of_A1`）を「ほぼ同語反復」と判定しました。ノートと xlsx はそう書いています。

## 8. 内部照合（2026-11-14、`pag2_internal_audit_249_256.md`）

- 前の定義と同じもの（Lean で確認）：`charU` は基本ファイル（Part 1）の `PAG.charFun` に `MulChar.toUnitHom` を通したものと同じ関数、`ip` は Part 249 の `ipG` の G = (ZMod N)ˣ の場合と同じ定義（範囲の中）。このパートはそれらを使わずに定義し直していた。
- 前の定理から直ちに出るもの（Lean で確認）：`eq_one_of_two`（Part 194 の `level_two_trivial`）、`not_isPrimitive_one_of_two_le`・`charU_one_mem_Vimprim`（Part 191 の `ne_one_of_isPrimitive`）、`not_isPrimitive_one_prime`（Part 28 の `prim_level_p_iff`）、`Vprim_two`（Part 26 の `no_prim_mod_two`）。
- 照合者 R3 の判定で数行で出るもの（C）：`ip_charU`（Part 214 の `sum_units_char` と付録 A の Part 3 の `conj_apply_eq_inv`）、`Vprim_ne_bot_prime`（確信度 低）。範囲の中の関係（Part 249・252 から。照合者の判定、Lean では未確認）：C は `JHL`・`TopL_charU`・`Vprim_ne_bot_three`・`TopL_charU_one_four`（低）、B は `ip_smul_smul`・`rootNum_ne_zero`。
- 前の鎖に見つからなかったもの（網羅ではない）：単数の上の作用素 T（`TopL`）、V_prim と V_imprim の分解と直交、V_prim の上のユニタリ性と一意性、V_imprim の上で等長でないこと。
- 限界：機械的な候補選び（型に現れる定数の近さ、上位 20 件）と Lean での直接の当てはめ、照合者の通読による。照合者は Grep が使えず、全宣言の文（約 2 万 2 千行）の 1〜3 割しか読めていない。「見つからなかった」は「ない」の証明ではない。
