# Part 256 の xlsx の行
HEAD = "PAG2.0-256 貼り合わせ U は素点ごとに分かれるか：互いに素な法での交差項の法則 W(χ₁χ₂) = s·χ₁(N)·χ₂(M)·W(χ₁)·W(χ₂)（著者が 2026-11-13 18:15 に候補 M1 を選んだ。すべて既知の事実の Lean 化：Montgomery–Vaughan の Theorem 9.6、Tate・Deligne の局所定数の GL(1)/ℚ の場合）"
ROWS = [
 ("cast_crtMap_fst", "分解の写像 crtMap（def：(a₁, a₂) ↦ a₁·N + a₂·M mod M·N）の法 M への像は a₁·N（補助）", "自然数の cast と N·M ≡ 0", "ZMod.cast_natCast, ZMod.natCast_zmod_val, ZMod.natCast_self"),
 ("cast_crtMap_snd", "分解の写像の法 N への像は a₂·M（補助）", "同じ", "ZMod.cast_natCast, ZMod.natCast_zmod_val, ZMod.natCast_self"),
 ("crtMap_bijective", "互いに素な法では分解の写像は全単射（中国剰余定理）", "単射（N は法 M の単数、M は法 N の単数）と濃度の一致", "ZMod.isUnit_iff_coprime, IsUnit.mul_left_injective, Fintype.bijective_iff_injective_and_card, ZMod.card"),
 ("stdAddChar_crtMap", "加法指標は分解で積に分かれる：e((a₁N + a₂M)/(MN)) = e(a₁/M)·e(a₂/N)", "指数関数の加法性と通分", "ZMod.stdAddChar_coe, Complex.exp_add, field_simp"),
 ("prodChar_apply", "積の指標 prodChar χ₁ χ₂（def：法 M·N）の値は χ₁(a mod M)·χ₂(a mod N)（単数でない a では両辺 0。互いに素は要らない）", "単数では changeLevel の値、単数でなければ M か N と共通因数を持つ", "DirichletCharacter.changeLevel_eq_cast_of_dvd, MulChar.map_nonunit, ZMod.isUnit_iff_coprime, Nat.Coprime.mul_right"),
 ("gaussSum_prodChar", "互いに素な法でのガウス和の乗法性：τ(χ₁χ₂) = χ₁(N)·χ₂(M)·τ(χ₁)·τ(χ₂)（原始性は要らない）", "和を分解の写像で付け替え、指標と加法指標を成分に分ける", "Function.Bijective.sum_comp, Fintype.sum_prod_type, Finset.sum_mul_sum, crtMap_bijective, stdAddChar_crtMap, prodChar_apply"),
 ("prodChar_neg_one", "(χ₁χ₂)(−1) = χ₁(−1)·χ₂(−1)（補助）", "prodChar_apply と −1 の還元", "ZMod.cast_neg, ZMod.cast_one"),
 ("crossSign_of_odd", "符号 crossSign（def：両方が奇なら −1、それ以外は 1）：両方が奇なら −1（補助）", "定義", "simp"),
 ("crossSign_of_even_left", "左が偶なら符号は 1（補助）", "偶なら奇でない", "simp"),
 ("crossSign_of_even_right", "右が偶なら符号は 1（補助）", "偶なら奇でない", "simp"),
 ("parFac_prodChar", "偶奇の因子のずれ：ε(χ₁χ₂) = s·ε(χ₁)·ε(χ₂)（ε = Part 252 の parFac は偶で 1、奇で −i。文献では無限素点の局所因子にあたる、は読み）", "偶奇の 4 通りの場合分け。両方が奇のとき (−i)(−i) = −1", "DirichletCharacter.even_or_odd, parFac_of_even, parFac_of_odd, Complex.I_mul_I"),
 ("rootNum_prodChar", "交差項の法則：W(χ₁χ₂) = s·χ₁(N)·χ₂(M)·W(χ₁)·W(χ₂)（互いに素な法。原始性は要らない）", "rootNum_eq と gaussSum_prodChar・parFac_prodChar、√(MN) = √M·√N", "rootNum_eq, Real.sqrt_mul, field_simp"),
 ("isPrimitive_prodChar", "互いに素な法の原始指標の積は原始（導手 = M·N）", "χ₁ = χ·χ₂⁻¹ の導手 M が lcm(cond χ, N) を割るので M ∣ cond χ。同様に N ∣ cond χ", "DirichletCharacter.conductor_mul_dvd_lcm_conductor, conductor_inv, conductor_changeLevel, Nat.Coprime.dvd_of_dvd_mul_right, Nat.Coprime.mul_dvd_of_dvd_of_dvd"),
 ("phaseA1_prodChar", "公準 A1 の位相（Part 254 の phaseA1）での交差項の法則（原始指標）", "原始なら phaseA1 = rootNum", "phaseA1_of_isPrimitive, isPrimitive_prodChar, rootNum_prodChar"),
 ("UA1_charU_prodChar", "貼り合わせ U（Part 254 の UA1）は、原始指標の積の関数を s·χ₁(N)·χ₂(M)·phaseA1(χ₁)·phaseA1(χ₂) 倍する（指標 1 つの上の固有値の式。作用素全体の等式ではない）", "UA1_charU と phaseA1_prodChar", "UA1_charU, phaseA1_prodChar"),
 ("cross_eq_sign_of_rootNum_one", "条件つきの文：W(χ₁) = W(χ₂) = W(χ₁χ₂) = 1 なら s·χ₁(N)·χ₂(M) = 1（2 次の指標では平方剰余の相互法則と同じ形。3 つの仮定は外から入れるもので、相互法則を示してはいない）", "rootNum_prodChar に代入", "rootNum_prodChar"),
 ("exists_primitive_odd_five", "証人：法 5 に奇の原始指標がある（補助）", "χ(−1) ≠ 1 の指標の存在", "DirichletCharacter.exists_apply_ne_one_of_hasEnoughRootsOfUnity, isPrimitive_of_prime_of_ne_one"),
 ("rootNum_prodChar_ne_mul", "中国剰余定理の成分の積とのずれの例：法 15 = 3·5 に、W(χ₁χ₂) ≠ W(χ₁)·W(χ₂) となる原始指標の組がある（両方が奇の組）", "s = −1、χ₁(5) = −1、χ₂(3)² = −1 なので比 χ₂(3) ≠ 1", "exists_primitive_odd_three, exists_primitive_odd_five, rootNum_prodChar, rootNum_ne_zero"),
 ("phaseA1_prodChar_ne_mul", "同じ例を公準 A1 の位相で：法 15 で phaseA1(χ₁χ₂) ≠ phaseA1(χ₁)·phaseA1(χ₂) となる原始指標の組がある", "rootNum_prodChar_ne_mul と原始性", "rootNum_prodChar_ne_mul, isPrimitive_prodChar, phaseA1_of_isPrimitive"),
 ("norm_char_unit", "単数での指標の値の絶対値は 1（Mathlib の unit_norm_eq_one と同じ証明。そのモジュールがこの環境で未ビルドのため。補助）", "単数群の位数乗が 1", "pow_eq_one_iff_of_nonneg, pow_card_eq_one'"),
 ("norm_cross", "交差項の絶対値は 1：互いに素な法で ‖χ₁(N)·χ₂(M)‖ = 1", "N は法 M の単数、M は法 N の単数", "ZMod.isUnit_iff_coprime, norm_char_unit"),
 ("charU_prodChar", "積の指標の関数は、中国剰余定理の 2 つの成分の関数の積：(χ₁χ₂)(u) = χ₁(u mod M)·χ₂(u mod N)", "prodChar_apply", "prodChar_apply"),
]
STEP_TEXT = "PAG 2.0 Part 256: PAG260.lean（貼り合わせ U は素点ごとに分かれるか：中国剰余定理の分解、互いに素な法でのガウス和の乗法性、偶奇の因子のずれ、交差項の法則 W(χ₁χ₂) = s·χ₁(N)·χ₂(M)·W(χ₁)·W(χ₂)、原始指標の積は原始、公準 A1 の位相と U の固有値での法則、法 15 の例、条件つきの文。22 項目と定義 3 個）をコンパイル"
STEP_NOTE = "2026-11-13、Part 256（著者が 18:15 に候補 M1 を選んだ）。数値照合 step279.py は 12 項目すべて合格（1 回目で通った。除去テスト (10)：互いに素を外すと両辺が 0）。試しのファイルで段階的にコンパイル（エラー・警告の内訳はノートの §3）。組み立ての 1 回目は docstring の位置の構文エラーで rc = 1、2 回目で rc = 0。pagpkg での本番のコンパイルはエラー・警告なし。公理は標準のものだけ（20 行が [propext, Classical.choice, Quot.sound]、2 行が [propext, Quot.sound]）。Mathlib の追加ビルドなし。独立照合（A・C・B）はノートの §7"
ENV_KEY = "Mathlib の追加ビルド（2026-11-13、Part 256）"
ENV_TEXT = "なし。PAG260 はビルド済みのモジュールだけを使う（import は PAG259）。Mathlib.NumberTheory.DirichletCharacter.Bounds は未ビルドのままで、unit_norm_eq_one と同じ証明を norm_char_unit として置いた"
