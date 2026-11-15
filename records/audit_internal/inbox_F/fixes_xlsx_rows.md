# xlsx（定理と証明）で変わった行（列 A 見出し・列 B Lean の名前・列 D 証明の方針）

## 行 3371：PAG2.0-251 P… `units_eq_of_coprime_parts`（列 D）
- 前：代表の合同を合わせる
- 後：代表の合同を合わせる（内部照合 2026-11-14：Part 192 の crt_unique から数行。照合者の判定、Lean で確認）

## 見出しの変更（行 3373 から始まる Part の全行に同じ）
- 前：PAG2.0-252 離散 Hartley 変換 H_N（正規化しない）と反転 J の合成 J∘H_N/√N は、単数の上で各原始指標 χ を W(χ) 倍する（単数の上の式はすべての指標で成り立つ。W は原始指標ならルート数）。読み：構築者が再構成したモノグラフ §1.3 の主張 (2)、U = J∘H_N/√N の原始指標の部分（公理 A1 の境界ユニタリの原始指標の部分）。U と A1 は Lean の文に出てこない（著者の判断 3「Lean 化してください」。重なりの読みはねじれた貼り合わせ U）
- 後：PAG2.0-252 離散 Hartley 変換 H_N（正規化しない）と反転 J の合成 J∘H_N/√N は、単数の上で各原始指標 χ を W(χ) 倍する（単数の上の式はすべての指標で成り立つ。W は原始指標ならルート数）。読み：構築者が再構成したモノグラフ §1.3 の主張 (2)、U = J∘H_N/√N の原始指標の部分（公理 A1 の境界ユニタリの原始指標の部分）。U と A1 は Lean の文に出てこない（著者の判断 3「Lean 化してください」。重なりの読みはねじれた貼り合わせ U）。内部照合（2026-11-14）：Hartley の部分は付録 A の Part 3（PAG3.lean、命題 2.8）とほぼ重なる。casKer は Part 3 の casK、rootNum は Part 192 の zN ÷ Part 194 の gs と同じ値

## 行 3373：PAG2.0-252 離… `casKer_eq`（列 D）
- 前：e(t) = exp(iθ)、e(−t) = exp(−iθ) に Euler の公式
- 後：e(t) = exp(iθ)、e(−t) = exp(−iθ) に Euler の公式（内部照合 2026-11-14：付録 A の Part 3 の casK_even_part・casK_odd_part から数行。照合者の判定）

## 行 3374：PAG2.0-252 離… `parFac_of_even`（列 D）
- 前：χ(−1) = 1 を代入
- 後：χ(−1) = 1 を代入（内部照合 2026-11-14：付録 A の Part 2 の parity_weight（r = 1）から [NeZero N] を外した形。照合者の判定）

## 行 3375：PAG2.0-252 離… `parFac_of_odd`（列 D）
- 前：χ(−1) = −1 を代入
- 後：χ(−1) = −1 を代入（内部照合 2026-11-14：付録 A の Part 2 の parity_weight（r = 1）から [NeZero N] を外した形。照合者の判定）

## 行 3376：PAG2.0-252 離… `inv_apply_neg_one`（列 D）
- 前：χ(−1) = ±1
- 後：χ(−1) = ±1（内部照合 2026-11-14：Part 5 の inv_apply_neg_one、Part 21 の chi_inv_neg_one、Part 77 の inv_neg_one と同じ文。Lean で確認）

## 行 3378：PAG2.0-252 離… `hartley_eq_of_isPrimitive`（列 D）
- 前：核を e(xy) と e(−xy) に分け、原始指標のガウス和の性質 gaussSum χ (e.mulShift y) = χ⁻¹(y)τ(χ) を 2 回使う
- 後：核を e(xy) と e(−xy) に分け、原始指標のガウス和の性質 gaussSum χ (e.mulShift y) = χ⁻¹(y)τ(χ) を 2 回使う（内部照合 2026-11-14：付録 A の Part 3 の hartley_char から数行。照合者の判定、確信度 低）

## 行 3379：PAG2.0-252 離… `hartley_eq_zero_of_not_isUnit`（列 D）
- 前：χ⁻¹(y) = 0
- 後：χ⁻¹(y) = 0（内部照合 2026-11-14：付録 A の Part 3 の hartley_char から数行。照合者の判定、確信度 低）

## 行 3380：PAG2.0-252 離… `rootNum_eq`（列 D）
- 前：偶奇で場合分け、1/i = −i
- 後：偶奇で場合分け、1/i = −i（内部照合 2026-11-14：付録 A の Part 2 の parity_weight から数行。照合者の判定）

## 行 3381：PAG2.0-252 離… `inv_apply_units_inv`（列 D）
- 前：χ(u)χ(u⁻¹) = 1
- 後：χ(u)χ(u⁻¹) = 1（内部照合 2026-11-14：付録 A の Part 3 の apply_inv_eq_inv_apply から 1 行。Lean で確認）

## 行 3382：PAG2.0-252 離… `JH_eq_rootNum_mul`（列 D）
- 前：hartley_eq_of_isPrimitive・rootNum_eq・inv_apply_units_inv
- 後：hartley_eq_of_isPrimitive・rootNum_eq・inv_apply_units_inv（内部照合 2026-11-14：付録 A の Part 3 の hartley_char から数行。照合者の判定、確信度 低）

## 行 3383：PAG2.0-252 離… `normSq_rootNum`（列 D）
- 前：|ε(χ)| = 1 と Part 16 の |τ(χ)|² = N
- 後：|ε(χ)| = 1 と Part 16 の |τ(χ)|² = N（内部照合 2026-11-14：Part 12 の normSq_gaussSum から数行。照合者の判定、Lean で確認）

## 行 3384：PAG2.0-252 離… `isPrimitive_of_prime_of_ne_one`（列 D）
- 前：導手は p を割るので 1 か p。1 なら自明な指標
- 後：導手は p を割るので 1 か p。1 なら自明な指標（内部照合 2026-11-14：Part 167 の primitive_of_ne_one と同じ文。Lean で確認）

## 行 3385：PAG2.0-252 離… `exists_primitive_odd_three`（列 D）
- 前：χ(−1) ≠ 1 となる指標をとる（指標の分離性）
- 後：χ(−1) ≠ 1 となる指標をとる（指標の分離性）（内部照合 2026-11-14：Part 115・163・167 の補題から数行。照合者の判定、Lean で確認）

## 行 3386：PAG2.0-252 離… `exists_primitive_even_five`（列 D）
- 前：χ(2) ≠ 1 の χ をとり、奇なら χ² を使う（−1 = 2·2 なので χ(2)² = −1）
- 後：χ(2) ≠ 1 の χ をとり、奇なら χ² を使う（−1 = 2·2 なので χ(2)² = −1）（内部照合 2026-11-14：Part 115・163・167 の補題から数行。照合者の判定）

## 行 3388：PAG2.0-252 離… `hartley_units_inv`（列 D）
- 前：x ↦ u·x の置換
- 後：x ↦ u·x の置換（内部照合 2026-11-14：付録 A の Part 3 の hartley_char から数行。照合者の判定、確信度 低）

## 行 3389：PAG2.0-252 離… `neg_one_mul_self`（列 D）
- 前：χ((−1)·(−1)) = χ(1)
- 後：χ((−1)·(−1)) = χ(1)（内部照合 2026-11-14：Part 5 の chi_neg_one_sq、Part 25 の chi_neg_one_sq' と同じ文。Lean で確認）

## 行 3390：PAG2.0-252 離… `sum_mul_stdAddChar_neg`（列 D）
- 前：x ↦ −x の置換
- 後：x ↦ −x の置換（内部照合 2026-11-14：付録 A の Part 3 の sum_neg_twist（x = 1）。Lean で確認）

## 行 3391：PAG2.0-252 離… `hartley_one`（列 D）
- 前：核を e(x) と e(−x) に分ける
- 後：核を e(x) と e(−x) に分ける（内部照合 2026-11-14：付録 A の Part 3 の hartley_char（命題 2.8）から数行。照合者の判定）

## 行 3392：PAG2.0-252 離… `JH_eq_rootNum_mul_any`（列 D）
- 前：hartley_units_inv・hartley_one・rootNum_eq
- 後：hartley_units_inv・hartley_one・rootNum_eq（内部照合 2026-11-14：付録 A の Part 3 の hartley_char から数行。照合者の判定、確信度 低）

## 見出しの変更（行 3395 から始まる Part の全行に同じ）
- 前：PAG2.0-253 原始部分での貼り合わせ U の作用素としての文（著者が着手前の候補 K1 を選んだ、21:17。重なりはねじれた貼り合わせ U と決定済み。A1 は位相の規約で、Lean の公理ではない）
- 後：PAG2.0-253 原始部分での貼り合わせ U の作用素としての文（著者が着手前の候補 K1 を選んだ、21:17。重なりはねじれた貼り合わせ U と決定済み。A1 は位相の規約で、Lean の公理ではない）。内部照合（2026-11-14）：charU は Part 1 の PAG.charFun（toUnitHom を通したもの）、ip は Part 249 の ipG と同じ対象

## 行 3400：PAG2.0-253 原… `ip_charU`（列 D）
- 前：conj χ(u) = χ⁻¹(u) と Part 218 の単数の上の指標の和
- 後：conj χ(u) = χ⁻¹(u) と Part 218 の単数の上の指標の和（内部照合 2026-11-14：Part 214 の sum_units_char と付録 A の Part 3 の conj_apply_eq_inv から数行。照合者の判定）

## 行 3422：PAG2.0-253 原… `not_isPrimitive_one_prime`（列 D）
- 前：導手の定義
- 後：導手の定義（内部照合 2026-11-14：Part 28 の prim_level_p_iff から 1 行。Lean で確認）

## 行 3424：PAG2.0-253 原… `Vprim_ne_bot_prime`（列 D）
- 前：χ(−1) ≠ 1 の指標は自明でなく、素数の法なので原始的
- 後：χ(−1) ≠ 1 の指標は自明でなく、素数の法なので原始的（内部照合 2026-11-14：Part 115 の Lc_ne_one と Part 167 の primitive_of_ne_one から数行。照合者の判定、確信度 低）

## 行 3425：PAG2.0-253 原… `not_isPrimitive_one_of_two_le`（列 D）
- 前：導手の定義
- 後：導手の定義（内部照合 2026-11-14：Part 191 の ne_one_of_isPrimitive の対偶。Lean で確認）

## 行 3426：PAG2.0-253 原… `charU_one_mem_Vimprim`（列 D）
- 前：生成元
- 後：生成元（内部照合 2026-11-14：Part 191 の ne_one_of_isPrimitive から 1 行。Lean で確認）

## 行 3427：PAG2.0-253 原… `eq_one_of_two`（列 D）
- 前：単数の上で比べる
- 後：単数の上で比べる（内部照合 2026-11-14：Part 194 の level_two_trivial から直ちに出る。Lean で確認）

## 行 3428：PAG2.0-253 原… `Vprim_two`（列 D）
- 前：法 2 の指標は自明で、自明な指標は原始的でない
- 後：法 2 の指標は自明で、自明な指標は原始的でない（内部照合 2026-11-14：Part 26 の no_prim_mod_two から出る。Lean で確認）

## 行 3433：PAG2.0-254 法… `rootNum_one_of_eq_one`（列 D）
- 前：法 1 のガウス和は 1、偶の指標
- 後：法 1 のガウス和は 1、偶の指標（内部照合 2026-11-14：Part 192 の zN_level_one から数行。照合者の判定、Lean で確認）

## 行 3434：PAG2.0-254 法… `phaseA1_one`（列 D）
- 前：自明な指標の導手は 1、誘導元は法 1 の自明な指標
- 後：自明な指標の導手は 1、誘導元は法 1 の自明な指標（内部照合 2026-11-14：Part 192 の zN_level_one から数行。照合者の判定、確信度 低）

## 行 3451：PAG2.0-254 法… `gaussSum_inv`（列 D）
- 前：共役は両方の指標を逆にし、加法的指標の逆は −1 倍のずらし
- 後：共役は両方の指標を逆にし、加法的指標の逆は −1 倍のずらし（内部照合 2026-11-14：Part 5 の conj_gaussSum と chi_neg_one_sq から 1 行。Lean で確認）

## 見出しの変更（行 3531 から始まる Part の全行に同じ）
- 前：PAG2.0-256 互いに素な法の原始指標の積の上での UA1 の固有値の式（読み：貼り合わせ U の固有値）：交差項の法則 W(χ₁χ₂) = s·χ₁(N)·χ₂(M)·W(χ₁)·W(χ₂)（著者が 2026-11-13 18:15 に候補 M1 を選んだ。既知の事実の Lean 化：Montgomery–Vaughan の Theorem 9.6 とそのルート数版。文献では、大域の ε 因子が局所の積であることと、不分岐なひねりでの局所 ε 因子の変化から出る形にあたる。局所 ε 因子は Lean にしていない）
- 後：PAG2.0-256 互いに素な法の原始指標の積の上での UA1 の固有値の式（読み：貼り合わせ U の固有値）：交差項の法則 W(χ₁χ₂) = s·χ₁(N)·χ₂(M)·W(χ₁)·W(χ₂)（著者が 2026-11-13 18:15 に候補 M1 を選んだ。既知の事実の Lean 化：Montgomery–Vaughan の Theorem 9.6 とそのルート数版。文献では、大域の ε 因子が局所の積であることと、不分岐なひねりでの局所 ε 因子の変化から出る形にあたる。局所 ε 因子は Lean にしていない）。内部照合（2026-11-14）：前半（中国剰余の分解 crtMap ＝ Part 189 の param、積の指標 prodChar ＝ Part 195 の cmul ＝ Part 232 の charMul、ガウス和の乗法性、原始性）は Part 189・190・195・232 の示し直し。crossSign は Part 194 の rs と同じ値。相互法則は Part 194 の real_reciprocity

## 行 3531：PAG2.0-256 互… `cast_crtMap_fst`（列 D）
- 前：自然数の cast と N·M ≡ 0
- 後：自然数の cast と N·M ≡ 0（内部照合 2026-11-14：Part 189 の param_cast₁ から直ちに出る。Lean で確認）

## 行 3532：PAG2.0-256 互… `cast_crtMap_snd`（列 D）
- 前：同じ
- 後：同じ（内部照合 2026-11-14：Part 189 の param_cast₂ から直ちに出る。Lean で確認）

## 行 3533：PAG2.0-256 互… `crtMap_bijective`（列 D）
- 前：単射（N は法 M の単数、M は法 N の単数）と濃度の一致
- 後：単射（N は法 M の単数、M は法 N の単数）と濃度の一致（内部照合 2026-11-14：Part 189 の param_bijective と同じ文。Lean で確認）

## 行 3534：PAG2.0-256 互… `stdAddChar_crtMap`（列 D）
- 前：指数関数の加法性と通分
- 後：指数関数の加法性と通分（内部照合 2026-11-14：Part 189 の stdAddChar_param と同じ文。Lean で確認）

## 行 3535：PAG2.0-256 互… `prodChar_apply`（列 D）
- 前：単数では changeLevel の値、単数でなければ M か N と共通因数を持つ
- 後：単数では changeLevel の値、単数でなければ M か N と共通因数を持つ（内部照合 2026-11-14：Part 189 の mul_changeLevel_apply、Part 195 の cmul_apply、Part 232 の charMul_apply と同じ文。Lean で確認）

## 行 3536：PAG2.0-256 互… `gaussSum_prodChar`（列 D）
- 前：和を分解の写像で付け替え、指標と加法指標を成分に分ける
- 後：和を分解の写像で付け替え、指標と加法指標を成分に分ける（内部照合 2026-11-14：Part 189 の gaussSum_mul_coprime と同じ文。Lean で確認。この Part はそれを使わずに示し直していた）

## 行 3537：PAG2.0-256 互… `prodChar_neg_one`（列 D）
- 前：prodChar_apply と −1 の還元
- 後：prodChar_apply と −1 の還元（内部照合 2026-11-14：Part 200 の changeLevel_neg_one を 2 回使うだけ。Lean で確認）

## 行 3541：PAG2.0-256 互… `parFac_prodChar`（列 D）
- 前：偶奇の 4 通りの場合分け。両方が奇のとき (−i)(−i) = −1
- 後：偶奇の 4 通りの場合分け。両方が奇のとき (−i)(−i) = −1（内部照合 2026-11-14：Part 200 の changeLevel_neg_one と Part 194 の neg_one_sq_eq から数行。Part 194 の gs_combine と同じ形。照合者の判定）

## 行 3542：PAG2.0-256 互… `rootNum_prodChar`（列 D）
- 前：rootNum_eq と gaussSum_prodChar・parFac_prodChar、√(MN) = √M·√N
- 後：rootNum_eq と gaussSum_prodChar・parFac_prodChar、√(MN) = √M·√N（内部照合 2026-11-14：中身は Part 189 の gaussSum_mul_coprime に偶奇の因子のずれを足したもの。照合者の判定は数行と新しいの境目）

## 行 3543：PAG2.0-256 互… `isPrimitive_prodChar`（列 D）
- 前：χ₁ = χ·χ₂⁻¹ の導手 M が lcm(cond χ, N) を割るので M ∣ cond χ。同様に N ∣ cond χ
- 後：χ₁ = χ·χ₂⁻¹ の導手 M が lcm(cond χ, N) を割るので M ∣ cond χ。同様に N ∣ cond χ（内部照合 2026-11-14：Part 190 の isPrimitive_mul、Part 232 の isPrimitive_charMul と同じ文。Lean で確認）

## 行 3546：PAG2.0-256 互… `cross_eq_sign_of_rootNum_one`（列 D）
- 前：rootNum_prodChar に代入
- 後：rootNum_prodChar に代入（内部照合 2026-11-14：実原始指標では 3 つの仮定は Part 194 の gauss_sign_real から成り立ち、結論は Part 194 の real_reciprocity と同じ式。相互法則そのものは Part 194 で仮定なしに示してある）

## 行 3551：PAG2.0-256 互… `norm_char_unit`（列 D）
- 前：単数群の位数乗が 1
- 後：単数群の位数乗が 1（内部照合 2026-11-14：Part 198 の normSq_chi_unit から数行。照合者の判定）

## 行 3552：PAG2.0-256 互… `norm_cross`（列 D）
- 前：N は法 M の単数、M は法 N の単数
- 後：N は法 M の単数、M は法 N の単数（内部照合 2026-11-14：Part 195 の normSq_chi_natCast から数行。照合者の判定）

## 行 3553：PAG2.0-256 互… `charU_prodChar`（列 D）
- 前：prodChar_apply
- 後：prodChar_apply（内部照合 2026-11-14：Part 232 の charMul_apply_unit から直ちに出る。Lean で確認）

## 見出しの変更（行 3561 から始まる Part の全行に同じ）
- 前：メモ：Part 1（行 2〜5）、Part 2（行 6〜15、定理 4.5）、Part 3（行 16〜31）、Part 4（行 32〜34、PAG4.lean）、PAG 2.0（行 35〜45、PAG5.lean）、PAG 2.0 Part 2（行 46〜53、PAG6.lean）、PAG 2.0 Part 3（行 54〜65、PAG7.lean）、PAG 2.0 Part 4（行 66〜74、PAG8.lean）、PAG 2.0 Part 5（行 75〜86、PAG9.lean）、PAG 2.0 Part 6（行 87〜98、PAG10.lean）、PAG 2.0 Part 7（行 99〜107、PAG11.lean）、PAG 2.0 Part 8（行 108〜119、PAG12.lean）、PAG 2.0 Part 9（行 120〜130、PAG13.lean）、PAG 2.0 Part 10（行 131〜144、PAG14.lean）、PAG 2.0 Part 11（行 145〜163、PAG15.lean）、PAG 2.0 Part 12（行 164〜171、PAG16.lean）、PAG 2.0 Part 13（行 172〜186、PAG17.lean）、PAG 2.0 Part 14（行 187〜194、PAG18.lean）、PAG 2.0 Part 15（行 195〜203、PAG19.lean）、PAG 2.0 Part 16（行 204〜207、PAG20.lean）、PAG 2.0 Part 17（行 208〜212、PAG21.lean）、PAG 2.0 Part 18（行 213〜220、PAG22.lean）、PAG 2.0 Part 19（行 221〜232、PAG23.lean）、PAG 2.0 Part 20（行 233〜241、PAG24.lean）、PAG 2.0 Part 21（行 242〜253、PAG25.lean）、PAG 2.0 Part 22（行 254〜263、PAG26.lean）、PAG 2.0 Part 23（行 264〜275、PAG27.lean）、PAG 2.0 Part 24（行 276〜295、PAG28.lean）、PAG 2.0 Part 25（行 296〜332、PAG29.lean）、PAG 2.0 Part 26（行 333〜353、PAG30.lean）、PAG 2.0 Part 27（行 354〜394、PAG31.lean）、PAG 2.0 Part 28（行 395〜423、PAG32.lean）、PAG 2.0 Part 29（行 424〜438、PAG33.lean）、PAG 2.0 Part 30（行 439〜453、PAG34.lean）、PAG 2.0 Part 31（行 454〜469、PAG35.lean）、PAG 2.0 Part 32（行 470〜476、PAG36.lean）、PAG 2.0 Part 33（行 477〜500、PAG37.lean）、PAG 2.0 Part 34（行 501〜508、PAG38.lean）、PAG 2.0 Part 35（行 509〜514、PAG39.lean）、PAG 2.0 Part 36（行 515〜518、PAG40.lean）、PAG 2.0 Part 37（行 519〜522、PAG41.lean）、PAG 2.0 Part 38（行 523〜526、PAG42.lean）、PAG 2.0 Part 39（行 527〜530、PAG43.lean）、PAG 2.0 Part 40（行 531〜555、PAG44.lean）、PAG 2.0 Part 41（行 556〜564、PAG45.lean）、PAG 2.0 Part 42（行 565〜571、PAG46.lean）、PAG 2.0 Part 43（行 572〜578、PAG47.lean）、PAG 2.0 Part 44（行 579〜582、PAG48.lean）、PAG 2.0 Part 45（行 583〜594、PAG49.lean）、PAG 2.0 Part 46（行 595〜599、PAG50.lean）、PAG 2.0 Part 47（行 600〜613、PAG51.lean）、PAG 2.0 Part 48（行 614〜622、PAG52.lean）、PAG 2.0 Part 49（行 623〜624、PAG53.lean）、PAG 2.0 Part 50（行 625〜630、PAG54.lean）、PAG 2.0 Part 51（行 631〜653、PAG55.lean）、PAG 2.0 Part 52（行 654〜660、PAG56.lean）、PAG 2.0 Part 53（行 661〜670、PAG57.lean）、PAG 2.0 Part 54（行 671〜689、PAG58.lean）、PAG 2.0 Part 55（行 690〜703、PAG59.lean）、PAG 2.0 Part 56（行 704〜706、PAG60.lean）、PAG 2.0 Part 57（行 707〜725、PAG61.lean）、PAG 2.0 Part 58（行 726〜734、PAG62.lean）、PAG 2.0 Part 59（行 735〜736、PAG63.lean）、PAG 2.0 Part 60（行 737〜740、PAG64.lean）、PAG 2.0 Part 61（行 741〜746、PAG65.lean）、PAG 2.0 Part 62（行 747〜751、PAG66.lean）、PAG 2.0 Part 63（行 752〜761、PAG67.lean）、PAG 2.0 Part 64（行 762〜771、PAG68.lean）、PAG 2.0 Part 65（行 772〜776、PAG69.lean）、PAG 2.0 Part 66（行 777〜780、PAG70.lean）、PAG 2.0 Part 67（行 781〜781、PAG71.lean）、PAG 2.0 Part 68（行 782〜789、PAG72.lean）、PAG 2.0 Part 69（行 790〜792、PAG73.lean）、PAG 2.0 Part 70（行 793〜797、PAG74.lean）、PAG 2.0 Part 71（行 798〜801、PAG75.lean）、PAG 2.0 Part 72（行 802〜802、PAG76.lean）、PAG 2.0 Part 73（行 803〜806、PAG77.lean）、PAG 2.0 Part 74（行 807〜810、PAG78.lean）、PAG 2.0 Part 75（行 811〜815、PAG79.lean）、PAG 2.0 Part 76（行 816〜822、PAG80.lean）、PAG 2.0 Part 77（行 823〜828、PAG81.lean）、PAG 2.0 Part 78（行 829〜833、PAG82.lean）、PAG 2.0 Part 79（行 834〜838、PAG83.lean）、PAG 2.0 Part 80（行 839〜843、PAG84.lean）、PAG 2.0 Part 81（行 844〜847、PAG85.lean）、PAG 2.0 Part 82（行 848〜849、PAG86.lean）、PAG 2.0 Part 83（行 850〜853、PAG87.lean）、PAG 2.0 Part 84（行 854〜858、PAG88.lean）、PAG 2.0 Part 85（行 859〜865、PAG89.lean）、PAG 2.0 Part 86（行 866〜872、PAG90.lean）、PAG 2.0 Part 87（行 873〜878、PAG91.lean）、PAG 2.0 Part 88（行 879〜881、PAG92.lean）、PAG 2.0 Part 89（行 882〜886、PAG93.lean）、PAG 2.0 Part 90（行 887〜891、PAG94.lean）、PAG 2.0 Part 91（行 892〜898、PAG95.lean）、PAG 2.0 Part 92（行 899〜905、PAG96.lean）、PAG 2.0 Part 93（行 906〜910、PAG97.lean）、PAG 2.0 Part 94（行 911〜917、PAG98.lean）、PAG 2.0 Part 95（行 918〜919、PAG99.lean）、PAG 2.0 Part 96（行 920〜923、PAG100.lean）、PAG 2.0 Part 97（行 924〜924、PAG101.lean）、PAG 2.0 Part 98（行 925〜927、PAG102.lean）、PAG 2.0 Part 99（行 928〜929、PAG103.lean）、PAG 2.0 Part 100（行 930〜930、PAG104.lean）、PAG 2.0 Part 101（行 931〜938、PAG105.lean）、PAG 2.0 Part 102（行 939〜944、PAG106.lean）、PAG 2.0 Part 103（行 945〜951、PAG107.lean）、PAG 2.0 Part 104（行 952〜965、PAG108.lean）、PAG 2.0 Part 105（行 966〜975、PAG109.lean）、PAG 2.0 Part 106（行 976〜987、PAG110.lean）、PAG 2.0 Part 107（行 988〜999、PAG111.lean）、PAG 2.0 Part 108（行 1000〜1005、PAG112.lean）、PAG 2.0 Part 109（行 1006〜1015、PAG113.lean）、PAG 2.0 Part 110（行 1016〜1025、PAG114.lean）、PAG 2.0 Part 111（行 1026〜1029、PAG115.lean）、PAG 2.0 Part 112（行 1030〜1037、PAG116.lean）、PAG 2.0 Part 113（行 1038〜1045、PAG117.lean）、PAG 2.0 Part 114（行 1046〜1054、PAG118.lean）、PAG 2.0 Part 115（行 1055〜1062、PAG119.lean）、PAG 2.0 Part 116（行 1063〜1073、PAG120.lean）、PAG 2.0 Part 117（行 1074〜1081、PAG121.lean）、PAG 2.0 Part 118（行 1082〜1089、PAG122.lean）、PAG 2.0 Part 119（行 1090〜1093、PAG123.lean）、PAG 2.0 Part 120（行 1094〜1100、PAG124.lean）、PAG 2.0 Part 121（行 1101〜1104、PAG125.lean）、PAG 2.0 Part 122（行 1105〜1108、PAG126.lean）、PAG 2.0 Part 123（行 1109〜1114、PAG127.lean）、PAG 2.0 Part 124（行 1115〜1119、PAG128.lean）、PAG 2.0 Part 125（行 1120〜1125、PAG129.lean）、PAG 2.0 Part 126（行 1126〜1128、PAG130.lean）、PAG 2.0 Part 127（行 1129〜1137、PAG131.lean）、PAG 2.0 Part 128（行 1138〜1142、PAG132.lean）、PAG 2.0 Part 129（行 1143〜1149、PAG133.lean）、PAG 2.0 Part 130（行 1150〜1159、PAG134.lean）、PAG 2.0 Part 131（行 1160〜1168、PAG135.lean）、PAG 2.0 Part 132（行 1169〜1174、PAG136.lean）、PAG 2.0 Part 133（行 1175〜1183、PAG137.lean）、PAG 2.0 Part 134（行 1184〜1187、PAG138.lean）、PAG 2.0 Part 135（行 1188〜1191、PAG139.lean）、PAG 2.0 Part 136（行 1192〜1197、PAG140.lean）、PAG 2.0 Part 137（行 1198〜1203、PAG141.lean）、PAG 2.0 Part 138（行 1204〜1208、PAG142.lean）、PAG 2.0 Part 139（行 1209〜1216、PAG143.lean）、PAG 2.0 Part 140（行 1217〜1220、PAG144.lean）、PAG 2.0 Part 141（行 1221〜1225、PAG145.lean）、PAG 2.0 Part 142（行 1226〜1229、PAG146.lean）、PAG 2.0 Part 143（行 1230〜1233、PAG147.lean）、PAG 2.0 Part 144（行 1234〜1236、PAG148.lean）、PAG 2.0 Part 145（行 1237〜1239、PAG149.lean）、PAG 2.0 Part 146（行 1240〜1242、PAG150.lean）、PAG 2.0 Part 147（行 1243〜1250、PAG151.lean）、PAG 2.0 Part 148（行 1251〜1256、PAG152.lean）、PAG 2.0 Part 149（行 1257〜1259、PAG153.lean）、PAG 2.0 Part 150（行 1260〜1266、PAG154.lean）、PAG 2.0 Part 151（行 1267〜1270、PAG155.lean）、PAG 2.0 Part 152（行 1271〜1272、PAG156.lean）、PAG 2.0 Part 153（行 1273〜1275、PAG157.lean）、PAG 2.0 Part 154（行 1276〜1277、PAG158.lean）、Part 155（行 1278〜1281、PAG159.lean）、Part 156（行 1282〜1289、PAG160.lean）、Part 157（行 1290〜1291、PAG161.lean）、Part 158（行 1292〜1301、PAG162.lean）、Part 159（行 1302〜1304、PAG163.lean）、Part 160（行 1305〜1309、PAG164.lean）、Part 161（行 1310〜1316、PAG165.lean）、Part 162（行 1317〜1325、PAG166.lean）、Part 163（行 1326〜1337、PAG167.lean）、Part 164（行 1338〜1341、PAG168.lean）、Part 165（行 1342〜1347、PAG169.lean）、Part 166（行 1348〜1351、PAG170.lean）、Part 167（行 1352〜1364、PAG171.lean）、Part 168（行 1365〜1370、PAG172.lean）、Part 169（行 1371〜1377、PAG173.lean）、Part 170（行 1378〜1383、PAG174.lean）、Part 171（行 1384〜1389、PAG175.lean）、Part 172（行 1390〜1395、PAG176.lean）、Part 173（行 1396〜1399、PAG177.lean）、Part 174（行 1400〜1404、PAG178.lean）、Part 175（行 1405〜1415、PAG179.lean）、Part 176（行 1416〜1423、PAG180.lean）、Part 177（行 1424〜1432、PAG181.lean）、Part 178（行 1433〜1440、PAG182.lean）、Part 179（行 1441〜1444、PAG183.lean）、Part 180（行 1445〜1458、PAG184.lean）、Part 181（行 1459〜1498、PAG185.lean）、Part 182（行 1499〜1510、PAG186.lean）、Part 183（行 1511〜1522、PAG187.lean）、Part 184（行 1523〜1528、PAG188.lean）、Part 185（行 1529〜1547、PAG189.lean）、Part 186（行 1548〜1582、PAG190.lean）、Part 187（行 1583〜1590、PAG191.lean）、Part 188（行 1591〜1598、PAG192.lean）、Part 189（行 1599〜1608、PAG193.lean）、Part 190（行 1609〜1625、PAG194.lean）、Part 191（行 1626〜1636、PAG195.lean）、Part 192（行 1637〜1656、PAG196.lean）、Part 193（行 1657〜1670、PAG197.lean）、Part 194（行 1671〜1700、PAG198.lean）、Part 195（行 1701〜1727、PAG199.lean）、Part 196（行 1728〜1742、PAG200.lean）、Part 197（行 1743〜1757、PAG201.lean）、Part 198（行 1758〜1772、PAG202.lean）、Part 199（行 1773〜1783、PAG203.lean）、Part 200（行 1784〜1799、PAG204.lean）、Part 201（行 1800〜1825、PAG205.lean）、Part 202（行 1826〜1848、PAG206.lean）、Part 203（行 1849〜1869、PAG207.lean）、Part 204（行 1870〜1904、PAG208.lean）、Part 205（行 1905〜1926、PAG209.lean）、Part 206（行 1927〜1942、PAG210.lean）、Part 207（行 1943〜1967、PAG211.lean）、Part 208（行 1968〜1988、PAG212.lean）、Part 209（行 1989〜2005、PAG213.lean）、Part 210（行 2006〜2025、PAG214.lean）、Part 211（行 2026〜2060、PAG215.lean）、Part 212（行 2061〜2081、PAG216.lean）、Part 213（行 2082〜2101、PAG217.lean）、Part 214（行 2102〜2144、PAG218.lean）、Part 215（行 2145〜2171、PAG219.lean）、Part 216（行 2172〜2199、PAG220.lean）、Part 217（行 2200〜2231、PAG221.lean）、Part 218（行 2232〜2250、PAG222.lean）、Part 219（行 2251〜2270、PAG223.lean）、Part 220（行 2271〜2302、PAG224.lean）、Part 221（行 2303〜2334、PAG225.lean）、Part 222（行 2335〜2370、PAG226.lean）、Part 223（行 2371〜2403、PAG227.lean）、Part 224（行 2404〜2424、PAG228.lean）、Part 225（行 2425〜2459、PAG229.lean）、Part 226（行 2460〜2496、PAG230.lean）、Part 227（行 2497〜2521、PAG231.lean）、Part 228（行 2522〜2564、PAG232.lean）、Part 229（行 2565〜2616、PAG233.lean）、Part 230（行 2617〜2642、PAG234.lean）、Part 231（行 2643〜2670、PAG235.lean）、Part 232（行 2671〜2712、PAG236.lean）、Part 233（行 2713〜2732、PAG237.lean）、Part 234（行 2733〜2751、PAG238.lean）、Part 235（行 2752〜2767、PAG239.lean）、Part 236（行 2768〜2806、PAG240.lean）、Part 237（行 2807〜2857、PAG241.lean）、Part 238（行 2858〜2881、PAG242.lean）、Part 239（行 2882〜2930、PAG243.lean）、Part 240（行 2931〜2971、PAG244.lean）、Part 241（行 2972〜3034、PAG245.lean）、Part 242（行 3035〜3068、PAG246.lean）、Part 243（行 3069〜3095、PAG247.lean）、Part 244（行 3096〜3129、PAG248.lean）、Part 245（行 3130〜3152、PAG249.lean）、Part 246（行 3153〜3189、PAG250.lean）、Part 247（行 3190〜3249、PAG251.lean）、Part 248（行 3250〜3282、PAG252.lean）、Part 249（行 3283〜3328、PAG253.lean）、Part 250（行 3329〜3356、PAG254.lean）、Part 251（行 3357〜3372、PAG255.lean）、Part 252（行 3373〜3394、PAG256.lean）、Part 253（行 3395〜3428、PAG257.lean）、Part 254（行 3429〜3485、PAG258.lean）、Part 255（行 3486〜3530、PAG259.lean）、Part 256（行 3531〜3553、PAG260.lean）。すべて Lean v4.36.0-rc1 と Mathlib（commit 2f3c7c8a）で 2026-10-17 にコンパイル（2026-10-22 に新しい環境で PAG.lean〜PAG186.lean をすべてコンパイルし直して確認。PAG187〜PAG199 は 2026-10-23、PAG200〜PAG213 は 2026-10-24、PAG214〜PAG216 は 2026-10-25、PAG217〜PAG220 は 2026-10-28、PAG221〜PAG230 は 2026-10-29、PAG231〜PAG236 は 2026-10-30、PAG237〜PAG239 は 2026-10-31 に同じ環境でコンパイル。2026-10-31 の夜に新しいコンテナで Lean と Mathlib を取り直し、PAG.lean〜PAG239.lean をすべてコンパイルし直して元の出力と照合した（途中で中断し、2026-11-04 に続きをコンパイル）。PAG240 は 2026-11-04 に同じ環境でコンパイル。PAG241 は 2026-11-04 に同じ環境でコンパイル（Mathlib の PiTensorProduct の 2 モジュールを追加でビルド）。PAG242 は 2026-11-05 に同じ環境でコンパイル（追加のビルドなし）。PAG243 は 2026-11-05 に同じ環境でコンパイル（追加のビルドなし）。PAG244 は 2026-11-05 に同じ環境でコンパイル（追加のビルドなし）。PAG245 は 2026-11-05 に同じ環境でコンパイル（追加のビルドなし）。PAG246 は 2026-11-05 に同じ環境でコンパイル（追加のビルドなし）。PAG247 は 2026-11-05 に同じ環境でコンパイル（追加のビルドなし）。PAG248 は 2026-11-05 に同じ環境でコンパイル（追加のビルドなし）。PAG249 は 2026-11-05 に同じ環境でコンパイル（追加のビルドなし）。PAG250 は 2026-11-06 にコンテナ再起動後の同じ環境でコンパイル（追加のビルドなし）。PAG251 も 2026-11-06 にコンテナ再起動後の同じ環境でコンパイル（追加のビルドなし）。PAG252 は 2026-11-07 にコンテナ再起動後の同じ環境でコンパイル（追加のビルドなし）。PAG253 も 2026-11-07 に同じ環境でコンパイル（追加のビルドなし）。PAG254 は 2026-11-11 に同じ環境でコンパイル（追加のビルドなし）。PAG255 は 2026-11-12 に同じ環境でコンパイル（追加のビルドなし）。PAG256 は 2026-11-12 に同じ環境でコンパイル（追加のビルドなし）。PAG257 は 2026-11-12 に同じ環境でコンパイル（追加のビルドなし）。PAG258 は 2026-11-13 に同じ環境でコンパイル（追加のビルドなし）。PAG259 は 2026-11-13 に同じ環境でコンパイル（追加のビルドなし）。PAG260 は 2026-11-13 に同じ環境でコンパイル（追加のビルドなし）。2026-11-14、著者側の補足3 による再照合のあと、PAG256・PAG258・PAG259・PAG260 の文面（冒頭の説明と docstring）だけを直し、PAG256〜PAG260 を同じ環境で組み立て直した（形式文は変えていない）。Part 252・254・255・256 の見出しと行の文面の一部も直した（行は足していない）。PAG37・PAG38・PAG39・PAG50 は前のチャットの記録から復元したもの）。sorry 0 個、警告なし。#print axioms はどれも propext、Classical.choice、Quot.sound のみ（sorryAx なし）。2026-10-24 の点検：PAG.lean〜PAG208.lean を空のディレクトリで最初からコンパイルし直し、208 本すべて成功、#print axioms 1903 項目すべて標準の公理、作業用の出力と一致。各ファイルで #print axioms の行がなかった補助補題 36 個（PAG.lean〜PAG181.lean の 19 本）は PAG_axioms_supplement.lean で確認（すべて標準の公理またはその一部）。Part 3 は追加の Mathlib ビルドなしで、PAG.lean・PAG2.lean を olean にして import した。未形式化：無限次元の部分（命題 2.3、定理 2.4、命題 3.2、定理 4.1）、命題 4.7・4.7a、§5.6 の局所計算。
- 後：メモ：Part 1（行 2〜5）、Part 2（行 6〜15、定理 4.5）、Part 3（行 16〜31）、Part 4（行 32〜34、PAG4.lean）、PAG 2.0（行 35〜45、PAG5.lean）、PAG 2.0 Part 2（行 46〜53、PAG6.lean）、PAG 2.0 Part 3（行 54〜65、PAG7.lean）、PAG 2.0 Part 4（行 66〜74、PAG8.lean）、PAG 2.0 Part 5（行 75〜86、PAG9.lean）、PAG 2.0 Part 6（行 87〜98、PAG10.lean）、PAG 2.0 Part 7（行 99〜107、PAG11.lean）、PAG 2.0 Part 8（行 108〜119、PAG12.lean）、PAG 2.0 Part 9（行 120〜130、PAG13.lean）、PAG 2.0 Part 10（行 131〜144、PAG14.lean）、PAG 2.0 Part 11（行 145〜163、PAG15.lean）、PAG 2.0 Part 12（行 164〜171、PAG16.lean）、PAG 2.0 Part 13（行 172〜186、PAG17.lean）、PAG 2.0 Part 14（行 187〜194、PAG18.lean）、PAG 2.0 Part 15（行 195〜203、PAG19.lean）、PAG 2.0 Part 16（行 204〜207、PAG20.lean）、PAG 2.0 Part 17（行 208〜212、PAG21.lean）、PAG 2.0 Part 18（行 213〜220、PAG22.lean）、PAG 2.0 Part 19（行 221〜232、PAG23.lean）、PAG 2.0 Part 20（行 233〜241、PAG24.lean）、PAG 2.0 Part 21（行 242〜253、PAG25.lean）、PAG 2.0 Part 22（行 254〜263、PAG26.lean）、PAG 2.0 Part 23（行 264〜275、PAG27.lean）、PAG 2.0 Part 24（行 276〜295、PAG28.lean）、PAG 2.0 Part 25（行 296〜332、PAG29.lean）、PAG 2.0 Part 26（行 333〜353、PAG30.lean）、PAG 2.0 Part 27（行 354〜394、PAG31.lean）、PAG 2.0 Part 28（行 395〜423、PAG32.lean）、PAG 2.0 Part 29（行 424〜438、PAG33.lean）、PAG 2.0 Part 30（行 439〜453、PAG34.lean）、PAG 2.0 Part 31（行 454〜469、PAG35.lean）、PAG 2.0 Part 32（行 470〜476、PAG36.lean）、PAG 2.0 Part 33（行 477〜500、PAG37.lean）、PAG 2.0 Part 34（行 501〜508、PAG38.lean）、PAG 2.0 Part 35（行 509〜514、PAG39.lean）、PAG 2.0 Part 36（行 515〜518、PAG40.lean）、PAG 2.0 Part 37（行 519〜522、PAG41.lean）、PAG 2.0 Part 38（行 523〜526、PAG42.lean）、PAG 2.0 Part 39（行 527〜530、PAG43.lean）、PAG 2.0 Part 40（行 531〜555、PAG44.lean）、PAG 2.0 Part 41（行 556〜564、PAG45.lean）、PAG 2.0 Part 42（行 565〜571、PAG46.lean）、PAG 2.0 Part 43（行 572〜578、PAG47.lean）、PAG 2.0 Part 44（行 579〜582、PAG48.lean）、PAG 2.0 Part 45（行 583〜594、PAG49.lean）、PAG 2.0 Part 46（行 595〜599、PAG50.lean）、PAG 2.0 Part 47（行 600〜613、PAG51.lean）、PAG 2.0 Part 48（行 614〜622、PAG52.lean）、PAG 2.0 Part 49（行 623〜624、PAG53.lean）、PAG 2.0 Part 50（行 625〜630、PAG54.lean）、PAG 2.0 Part 51（行 631〜653、PAG55.lean）、PAG 2.0 Part 52（行 654〜660、PAG56.lean）、PAG 2.0 Part 53（行 661〜670、PAG57.lean）、PAG 2.0 Part 54（行 671〜689、PAG58.lean）、PAG 2.0 Part 55（行 690〜703、PAG59.lean）、PAG 2.0 Part 56（行 704〜706、PAG60.lean）、PAG 2.0 Part 57（行 707〜725、PAG61.lean）、PAG 2.0 Part 58（行 726〜734、PAG62.lean）、PAG 2.0 Part 59（行 735〜736、PAG63.lean）、PAG 2.0 Part 60（行 737〜740、PAG64.lean）、PAG 2.0 Part 61（行 741〜746、PAG65.lean）、PAG 2.0 Part 62（行 747〜751、PAG66.lean）、PAG 2.0 Part 63（行 752〜761、PAG67.lean）、PAG 2.0 Part 64（行 762〜771、PAG68.lean）、PAG 2.0 Part 65（行 772〜776、PAG69.lean）、PAG 2.0 Part 66（行 777〜780、PAG70.lean）、PAG 2.0 Part 67（行 781〜781、PAG71.lean）、PAG 2.0 Part 68（行 782〜789、PAG72.lean）、PAG 2.0 Part 69（行 790〜792、PAG73.lean）、PAG 2.0 Part 70（行 793〜797、PAG74.lean）、PAG 2.0 Part 71（行 798〜801、PAG75.lean）、PAG 2.0 Part 72（行 802〜802、PAG76.lean）、PAG 2.0 Part 73（行 803〜806、PAG77.lean）、PAG 2.0 Part 74（行 807〜810、PAG78.lean）、PAG 2.0 Part 75（行 811〜815、PAG79.lean）、PAG 2.0 Part 76（行 816〜822、PAG80.lean）、PAG 2.0 Part 77（行 823〜828、PAG81.lean）、PAG 2.0 Part 78（行 829〜833、PAG82.lean）、PAG 2.0 Part 79（行 834〜838、PAG83.lean）、PAG 2.0 Part 80（行 839〜843、PAG84.lean）、PAG 2.0 Part 81（行 844〜847、PAG85.lean）、PAG 2.0 Part 82（行 848〜849、PAG86.lean）、PAG 2.0 Part 83（行 850〜853、PAG87.lean）、PAG 2.0 Part 84（行 854〜858、PAG88.lean）、PAG 2.0 Part 85（行 859〜865、PAG89.lean）、PAG 2.0 Part 86（行 866〜872、PAG90.lean）、PAG 2.0 Part 87（行 873〜878、PAG91.lean）、PAG 2.0 Part 88（行 879〜881、PAG92.lean）、PAG 2.0 Part 89（行 882〜886、PAG93.lean）、PAG 2.0 Part 90（行 887〜891、PAG94.lean）、PAG 2.0 Part 91（行 892〜898、PAG95.lean）、PAG 2.0 Part 92（行 899〜905、PAG96.lean）、PAG 2.0 Part 93（行 906〜910、PAG97.lean）、PAG 2.0 Part 94（行 911〜917、PAG98.lean）、PAG 2.0 Part 95（行 918〜919、PAG99.lean）、PAG 2.0 Part 96（行 920〜923、PAG100.lean）、PAG 2.0 Part 97（行 924〜924、PAG101.lean）、PAG 2.0 Part 98（行 925〜927、PAG102.lean）、PAG 2.0 Part 99（行 928〜929、PAG103.lean）、PAG 2.0 Part 100（行 930〜930、PAG104.lean）、PAG 2.0 Part 101（行 931〜938、PAG105.lean）、PAG 2.0 Part 102（行 939〜944、PAG106.lean）、PAG 2.0 Part 103（行 945〜951、PAG107.lean）、PAG 2.0 Part 104（行 952〜965、PAG108.lean）、PAG 2.0 Part 105（行 966〜975、PAG109.lean）、PAG 2.0 Part 106（行 976〜987、PAG110.lean）、PAG 2.0 Part 107（行 988〜999、PAG111.lean）、PAG 2.0 Part 108（行 1000〜1005、PAG112.lean）、PAG 2.0 Part 109（行 1006〜1015、PAG113.lean）、PAG 2.0 Part 110（行 1016〜1025、PAG114.lean）、PAG 2.0 Part 111（行 1026〜1029、PAG115.lean）、PAG 2.0 Part 112（行 1030〜1037、PAG116.lean）、PAG 2.0 Part 113（行 1038〜1045、PAG117.lean）、PAG 2.0 Part 114（行 1046〜1054、PAG118.lean）、PAG 2.0 Part 115（行 1055〜1062、PAG119.lean）、PAG 2.0 Part 116（行 1063〜1073、PAG120.lean）、PAG 2.0 Part 117（行 1074〜1081、PAG121.lean）、PAG 2.0 Part 118（行 1082〜1089、PAG122.lean）、PAG 2.0 Part 119（行 1090〜1093、PAG123.lean）、PAG 2.0 Part 120（行 1094〜1100、PAG124.lean）、PAG 2.0 Part 121（行 1101〜1104、PAG125.lean）、PAG 2.0 Part 122（行 1105〜1108、PAG126.lean）、PAG 2.0 Part 123（行 1109〜1114、PAG127.lean）、PAG 2.0 Part 124（行 1115〜1119、PAG128.lean）、PAG 2.0 Part 125（行 1120〜1125、PAG129.lean）、PAG 2.0 Part 126（行 1126〜1128、PAG130.lean）、PAG 2.0 Part 127（行 1129〜1137、PAG131.lean）、PAG 2.0 Part 128（行 1138〜1142、PAG132.lean）、PAG 2.0 Part 129（行 1143〜1149、PAG133.lean）、PAG 2.0 Part 130（行 1150〜1159、PAG134.lean）、PAG 2.0 Part 131（行 1160〜1168、PAG135.lean）、PAG 2.0 Part 132（行 1169〜1174、PAG136.lean）、PAG 2.0 Part 133（行 1175〜1183、PAG137.lean）、PAG 2.0 Part 134（行 1184〜1187、PAG138.lean）、PAG 2.0 Part 135（行 1188〜1191、PAG139.lean）、PAG 2.0 Part 136（行 1192〜1197、PAG140.lean）、PAG 2.0 Part 137（行 1198〜1203、PAG141.lean）、PAG 2.0 Part 138（行 1204〜1208、PAG142.lean）、PAG 2.0 Part 139（行 1209〜1216、PAG143.lean）、PAG 2.0 Part 140（行 1217〜1220、PAG144.lean）、PAG 2.0 Part 141（行 1221〜1225、PAG145.lean）、PAG 2.0 Part 142（行 1226〜1229、PAG146.lean）、PAG 2.0 Part 143（行 1230〜1233、PAG147.lean）、PAG 2.0 Part 144（行 1234〜1236、PAG148.lean）、PAG 2.0 Part 145（行 1237〜1239、PAG149.lean）、PAG 2.0 Part 146（行 1240〜1242、PAG150.lean）、PAG 2.0 Part 147（行 1243〜1250、PAG151.lean）、PAG 2.0 Part 148（行 1251〜1256、PAG152.lean）、PAG 2.0 Part 149（行 1257〜1259、PAG153.lean）、PAG 2.0 Part 150（行 1260〜1266、PAG154.lean）、PAG 2.0 Part 151（行 1267〜1270、PAG155.lean）、PAG 2.0 Part 152（行 1271〜1272、PAG156.lean）、PAG 2.0 Part 153（行 1273〜1275、PAG157.lean）、PAG 2.0 Part 154（行 1276〜1277、PAG158.lean）、Part 155（行 1278〜1281、PAG159.lean）、Part 156（行 1282〜1289、PAG160.lean）、Part 157（行 1290〜1291、PAG161.lean）、Part 158（行 1292〜1301、PAG162.lean）、Part 159（行 1302〜1304、PAG163.lean）、Part 160（行 1305〜1309、PAG164.lean）、Part 161（行 1310〜1316、PAG165.lean）、Part 162（行 1317〜1325、PAG166.lean）、Part 163（行 1326〜1337、PAG167.lean）、Part 164（行 1338〜1341、PAG168.lean）、Part 165（行 1342〜1347、PAG169.lean）、Part 166（行 1348〜1351、PAG170.lean）、Part 167（行 1352〜1364、PAG171.lean）、Part 168（行 1365〜1370、PAG172.lean）、Part 169（行 1371〜1377、PAG173.lean）、Part 170（行 1378〜1383、PAG174.lean）、Part 171（行 1384〜1389、PAG175.lean）、Part 172（行 1390〜1395、PAG176.lean）、Part 173（行 1396〜1399、PAG177.lean）、Part 174（行 1400〜1404、PAG178.lean）、Part 175（行 1405〜1415、PAG179.lean）、Part 176（行 1416〜1423、PAG180.lean）、Part 177（行 1424〜1432、PAG181.lean）、Part 178（行 1433〜1440、PAG182.lean）、Part 179（行 1441〜1444、PAG183.lean）、Part 180（行 1445〜1458、PAG184.lean）、Part 181（行 1459〜1498、PAG185.lean）、Part 182（行 1499〜1510、PAG186.lean）、Part 183（行 1511〜1522、PAG187.lean）、Part 184（行 1523〜1528、PAG188.lean）、Part 185（行 1529〜1547、PAG189.lean）、Part 186（行 1548〜1582、PAG190.lean）、Part 187（行 1583〜1590、PAG191.lean）、Part 188（行 1591〜1598、PAG192.lean）、Part 189（行 1599〜1608、PAG193.lean）、Part 190（行 1609〜1625、PAG194.lean）、Part 191（行 1626〜1636、PAG195.lean）、Part 192（行 1637〜1656、PAG196.lean）、Part 193（行 1657〜1670、PAG197.lean）、Part 194（行 1671〜1700、PAG198.lean）、Part 195（行 1701〜1727、PAG199.lean）、Part 196（行 1728〜1742、PAG200.lean）、Part 197（行 1743〜1757、PAG201.lean）、Part 198（行 1758〜1772、PAG202.lean）、Part 199（行 1773〜1783、PAG203.lean）、Part 200（行 1784〜1799、PAG204.lean）、Part 201（行 1800〜1825、PAG205.lean）、Part 202（行 1826〜1848、PAG206.lean）、Part 203（行 1849〜1869、PAG207.lean）、Part 204（行 1870〜1904、PAG208.lean）、Part 205（行 1905〜1926、PAG209.lean）、Part 206（行 1927〜1942、PAG210.lean）、Part 207（行 1943〜1967、PAG211.lean）、Part 208（行 1968〜1988、PAG212.lean）、Part 209（行 1989〜2005、PAG213.lean）、Part 210（行 2006〜2025、PAG214.lean）、Part 211（行 2026〜2060、PAG215.lean）、Part 212（行 2061〜2081、PAG216.lean）、Part 213（行 2082〜2101、PAG217.lean）、Part 214（行 2102〜2144、PAG218.lean）、Part 215（行 2145〜2171、PAG219.lean）、Part 216（行 2172〜2199、PAG220.lean）、Part 217（行 2200〜2231、PAG221.lean）、Part 218（行 2232〜2250、PAG222.lean）、Part 219（行 2251〜2270、PAG223.lean）、Part 220（行 2271〜2302、PAG224.lean）、Part 221（行 2303〜2334、PAG225.lean）、Part 222（行 2335〜2370、PAG226.lean）、Part 223（行 2371〜2403、PAG227.lean）、Part 224（行 2404〜2424、PAG228.lean）、Part 225（行 2425〜2459、PAG229.lean）、Part 226（行 2460〜2496、PAG230.lean）、Part 227（行 2497〜2521、PAG231.lean）、Part 228（行 2522〜2564、PAG232.lean）、Part 229（行 2565〜2616、PAG233.lean）、Part 230（行 2617〜2642、PAG234.lean）、Part 231（行 2643〜2670、PAG235.lean）、Part 232（行 2671〜2712、PAG236.lean）、Part 233（行 2713〜2732、PAG237.lean）、Part 234（行 2733〜2751、PAG238.lean）、Part 235（行 2752〜2767、PAG239.lean）、Part 236（行 2768〜2806、PAG240.lean）、Part 237（行 2807〜2857、PAG241.lean）、Part 238（行 2858〜2881、PAG242.lean）、Part 239（行 2882〜2930、PAG243.lean）、Part 240（行 2931〜2971、PAG244.lean）、Part 241（行 2972〜3034、PAG245.lean）、Part 242（行 3035〜3068、PAG246.lean）、Part 243（行 3069〜3095、PAG247.lean）、Part 244（行 3096〜3129、PAG248.lean）、Part 245（行 3130〜3152、PAG249.lean）、Part 246（行 3153〜3189、PAG250.lean）、Part 247（行 3190〜3249、PAG251.lean）、Part 248（行 3250〜3282、PAG252.lean）、Part 249（行 3283〜3328、PAG253.lean）、Part 250（行 3329〜3356、PAG254.lean）、Part 251（行 3357〜3372、PAG255.lean）、Part 252（行 3373〜3394、PAG256.lean）、Part 253（行 3395〜3428、PAG257.lean）、Part 254（行 3429〜3485、PAG258.lean）、Part 255（行 3486〜3530、PAG259.lean）、Part 256（行 3531〜3553、PAG260.lean）。すべて Lean v4.36.0-rc1 と Mathlib（commit 2f3c7c8a）で 2026-10-17 にコンパイル（2026-10-22 に新しい環境で PAG.lean〜PAG186.lean をすべてコンパイルし直して確認。PAG187〜PAG199 は 2026-10-23、PAG200〜PAG213 は 2026-10-24、PAG214〜PAG216 は 2026-10-25、PAG217〜PAG220 は 2026-10-28、PAG221〜PAG230 は 2026-10-29、PAG231〜PAG236 は 2026-10-30、PAG237〜PAG239 は 2026-10-31 に同じ環境でコンパイル。2026-10-31 の夜に新しいコンテナで Lean と Mathlib を取り直し、PAG.lean〜PAG239.lean をすべてコンパイルし直して元の出力と照合した（途中で中断し、2026-11-04 に続きをコンパイル）。PAG240 は 2026-11-04 に同じ環境でコンパイル。PAG241 は 2026-11-04 に同じ環境でコンパイル（Mathlib の PiTensorProduct の 2 モジュールを追加でビルド）。PAG242 は 2026-11-05 に同じ環境でコンパイル（追加のビルドなし）。PAG243 は 2026-11-05 に同じ環境でコンパイル（追加のビルドなし）。PAG244 は 2026-11-05 に同じ環境でコンパイル（追加のビルドなし）。PAG245 は 2026-11-05 に同じ環境でコンパイル（追加のビルドなし）。PAG246 は 2026-11-05 に同じ環境でコンパイル（追加のビルドなし）。PAG247 は 2026-11-05 に同じ環境でコンパイル（追加のビルドなし）。PAG248 は 2026-11-05 に同じ環境でコンパイル（追加のビルドなし）。PAG249 は 2026-11-05 に同じ環境でコンパイル（追加のビルドなし）。PAG250 は 2026-11-06 にコンテナ再起動後の同じ環境でコンパイル（追加のビルドなし）。PAG251 も 2026-11-06 にコンテナ再起動後の同じ環境でコンパイル（追加のビルドなし）。PAG252 は 2026-11-07 にコンテナ再起動後の同じ環境でコンパイル（追加のビルドなし）。PAG253 も 2026-11-07 に同じ環境でコンパイル（追加のビルドなし）。PAG254 は 2026-11-11 に同じ環境でコンパイル（追加のビルドなし）。PAG255 は 2026-11-12 に同じ環境でコンパイル（追加のビルドなし）。PAG256 は 2026-11-12 に同じ環境でコンパイル（追加のビルドなし）。PAG257 は 2026-11-12 に同じ環境でコンパイル（追加のビルドなし）。PAG258 は 2026-11-13 に同じ環境でコンパイル（追加のビルドなし）。PAG259 は 2026-11-13 に同じ環境でコンパイル（追加のビルドなし）。PAG260 は 2026-11-13 に同じ環境でコンパイル（追加のビルドなし）。2026-11-14、著者側の補足3 による再照合のあと、PAG256・PAG258・PAG259・PAG260 の文面（冒頭の説明と docstring）だけを直し、PAG256〜PAG260 を同じ環境で組み立て直した（形式文は変えていない）。Part 252・254・255・256 の見出しと行の文面の一部も直した（行は足していない）。PAG37・PAG38・PAG39・PAG50 は前のチャットの記録から復元したもの）。sorry 0 個、警告なし。#print axioms はどれも propext、Classical.choice、Quot.sound のみ（sorryAx なし）。2026-10-24 の点検：PAG.lean〜PAG208.lean を空のディレクトリで最初からコンパイルし直し、208 本すべて成功、#print axioms 1903 項目すべて標準の公理、作業用の出力と一致。各ファイルで #print axioms の行がなかった補助補題 36 個（PAG.lean〜PAG181.lean の 19 本）は PAG_axioms_supplement.lean で確認（すべて標準の公理またはその一部）。Part 3 は追加の Mathlib ビルドなしで、PAG.lean・PAG2.lean を olean にして import した。未形式化：無限次元の部分（命題 2.3、定理 2.4、命題 3.2、定理 4.1）、命題 4.7・4.7a、§5.6 の局所計算。2026-11-14、内部照合（Part 249〜256 の宣言を前の鎖と突き合わせた監査）のあと、PAG255〜PAG258・PAG260 の docstring と冒頭の説明に注記を足し、PAG255〜PAG260 を同じ環境で組み立て直した（形式文は変えていない）。Part 251〜256 の行の「証明の方針」と、Part 252・253・256 の見出しに注記を足した（行は足していない）。

## 検証手順の追加行（手順 278）
- 278 | 内部照合の監査（2026-11-14、著者の判断）：Part 249〜256（PAG253〜PAG260）の宣言 334 件を、前の鎖（PAG.lean〜PAG252.lean と PAG3・PAG5・PAG6）と突き合わせた。Lean のメタプログラムで全宣言の定数を書き出し（4279 件）、候補を機械的に選び、一方を他方にそのまま当てる確認を約 1 万 3 千組。独立の照合者 5 人（R1〜R5）に形式文の全文を渡して判定させ、A・B の判定を Lean で確かめた。重複を docstring・冒頭・ノート・表に書き足し、PAG255〜PAG260 を組み立て直した | 完了 | 前の鎖と同じ文・同じ対象（A）と直ちに出るもの（B）を Lean で確認：Part 252 に 7、Part 253 に 6（範囲の中の ip を含めず）、Part 254 に 1、Part 256 に 12（定義 3 を含む）、計 26。照合者の判定で前の鎖から数行で出るもの（C）は 20（4 件を Lean で確認、すべて当たり）。Part 249・250・255 は前の鎖に重複なし。照合者は Grep が使えず、全宣言の文の 1〜3 割しか読めていない。記録は pag2_internal_audit_249_256.md
