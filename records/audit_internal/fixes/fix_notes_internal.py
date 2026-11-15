# 内部照合（2026-11-14）の結果を Part 249〜256 のノートに書き足す（節の追加と、誤解を招く箇所への短い追記）。
import os
D = '/home/claude/out185'
REP = '`pag2_internal_audit_249_256.md`'
LIM = ('- 限界：機械的な候補選び（型に現れる定数の近さ、上位 20 件）と Lean での直接の当てはめ、照合者の通読による。照合者は Grep が使えず、'
       '全宣言の文（約 2 万 2 千行）の 1〜3 割しか読めていない。「見つからなかった」は「ない」の証明ではない。')
SEC = {
 'pag2_part249_idele_class_density.md': ('8', [
  '- 前の鎖（PAG.lean〜PAG252.lean と、鎖に import されていない付録 A・PAG 2.0 の初めのファイル PAG3・PAG5・PAG6）に、このパートの宣言と同じ文・直ちに出る文・数行で出る文は見つからなかった（照合者 R1、機械的な照合）。',
  '- 一般化の関係（示し直しではなく、前の文を特別な場合として含む形）：`ipG` は Part 48 の `ip`・Part 225 の `herm`（法 N の上の内積）を任意の有限型に広げた定義。`ipG_smul_left`・`ipG_smul_right` は Part 51 の `ip_smul_left`・`ip_smul_right`、Part 213 の `inner_smul_left\'`、Part 225 の `herm_smul_left`・`herm_smul_right` を含む（前の文がこちらから出ることを Lean で確認）。照合者の判定では、`kUnit_mul_natCast`・`unitsMap_kUnit` は Part 33 の `five_val`・`unitsMap_five` の一般化、`mem_dilCommute_of_prime` は Part 220 の `mem_dilCommute` を強めた形。',
  '- 定理 2.6 の部分は、基本ファイル（Part 1、PAG.lean）の `eigen_of_commute`・`real_sector_sign` を使って組み立てている（示し直しではない）。',
 ]),
 'pag2_part250_resolution_emergence.md': ('8', [
  '- 前の鎖に、このパートの宣言と同じ文・直ちに出る文・数行で出る文は見つからなかった（照合者 R1、機械的な照合）。',
  '- 範囲の中の関係：`dense_logSet_coprime` は Part 249 の `exists_cls_near` から直ちに出る（照合者の判定 B）。`dense_logSet` も同じ定理から数行（C）。',
 ]),
 'pag2_part251_projective_limit.md': ('8', [
  '- `units_eq_of_coprime_parts` は Part 192（PAG196）の `crt_unique` から数行で出る（照合者 R2 の判定 C。Lean で確認：`audit_internal/lean/SampleC.lean`）。',
  '- 範囲の中の関係：`kUnit_congr` は Part 249 の `kUnit_mul_natCast` から数行（C）。',
  '- そのほかの主な文（射影系 `unitSys`、素数の類の系 `primeSys`、稠密性 `dense_closure_primeGens` など）は、前の鎖に見つからなかった。',
 ]),
 'pag2_part252_hartley_gluing.md': ('9', [
  '- **Hartley の部分は、付録 A の Part 3（PAG3.lean、命題 2.8）とほぼ重なっていた。** PAG3.lean は鎖に import されていない初めのファイルで、`casK`（Hartley の核）、`casK_even_part`・`casK_odd_part`、`sum_neg_twist`、`hartley_char`（Σ_y cas(xy)χ(y) = (偶 1／奇 −i)·Σ_y e(xy/N)χ(y)）、`apply_inv_eq_inv_apply` がある。xlsx では「命題 2.8」「付録 A.2 の注記」の行。',
  '- 前の鎖に同じ文・同じ値の定義があるもの（Lean で確認）：',
  '  - `inv_apply_neg_one`：Part 5 の `inv_apply_neg_one`、Part 21 の `chi_inv_neg_one`、Part 77 の `inv_neg_one` と同じ文。',
  '  - `neg_one_mul_self`：Part 5 の `chi_neg_one_sq`、Part 25 の `chi_neg_one_sq\'` と同じ文。',
  '  - `isPrimitive_of_prime_of_ne_one`：Part 167 の `primitive_of_ne_one` と同じ文。',
  '  - `casKer`：付録 A の Part 3 の `casK` と同じ値（式の書き方は違う）。',
  '  - `rootNum`：Part 192 の `zN` を Part 194 の `gs` で割ったものと同じ値。',
  '  - `inv_apply_units_inv`・`sum_mul_stdAddChar_neg`：付録 A の Part 3 の `apply_inv_eq_inv_apply`・`sum_neg_twist`（x = 1）から 1 行。',
  '- 照合者 R2 の判定で数行で出るもの（C）：`hartley_one`・`hartley_eq_of_isPrimitive`・`hartley_eq_zero_of_not_isUnit`・`hartley_units_inv`・`JH_eq_rootNum_mul`・`JH_eq_rootNum_mul_any`・`casKer_eq`（付録 A の Part 3 の `hartley_char` などから。うち 5 件は確信度 低）、`normSq_rootNum`（Part 12 の `normSq_gaussSum` から。Lean で確認）、`exists_primitive_odd_three`（Part 115・163・167 から。Lean で確認）・`exists_primitive_even_five`、`parFac`・`rootNum_eq`（Part 194 の `gs`、付録 A の Part 2 の `parity_weight`）。`parFac_of_even`・`parFac_of_odd` は付録 A の Part 2 の `parity_weight`（r = 1）から [NeZero N] を外した形。',
  '- **鎖に新しいもの**：変換としての定義（`hartley`・`JH`）と、原始性を外したときの反例（`removal_counterexample`・`removal_counterexample_four`・`removal_counterexample_normSq`）。',
  '- §1 の位置づけ「既知の事実の書き直し（再導出）」は変わらない。加えて、鎖の中では付録 A の Part 3 の命題 2.8 の再導出だった。冒頭の「Hartley の形の文献は見つからず」は外の文献についての記録で、自分の鎖には命題 2.8 があった。',
 ]),
 'pag2_part253_primitive_operator.md': ('8', [
  '- 前の定義と同じ対象：`charU` は基本ファイル（Part 1）の `PAG.charFun` に `MulChar.toUnitHom` を通したもの、`ip` は Part 249 の `ipG` の G = (ZMod N)ˣ の場合（Lean で確認）。このパートはそれらを使わずに定義し直していた。',
  '- 前の定理から直ちに出るもの（Lean で確認）：`eq_one_of_two`（Part 194 の `level_two_trivial`）、`not_isPrimitive_one_of_two_le`・`charU_one_mem_Vimprim`（Part 191 の `ne_one_of_isPrimitive`）、`not_isPrimitive_one_prime`（Part 28 の `prim_level_p_iff`）、`Vprim_two`（Part 26 の `no_prim_mod_two`）。',
  '- 照合者 R3 の判定で数行で出るもの（C）：`ip_charU`（Part 214 の `sum_units_char` と付録 A の Part 3 の `conj_apply_eq_inv`）、`Vprim_ne_bot_prime`（確信度 低）。範囲の中の関係（Part 252 から）：`JHL`・`TopL_charU`・`Vprim_ne_bot_three`・`TopL_charU_one_four`（低）、`ip_smul_smul`・`rootNum_ne_zero`。',
  '- 鎖に新しいもの：単数の上の作用素 T（`TopL`）、V_prim と V_imprim の分解と直交、V_prim の上のユニタリ性と一意性、V_imprim の上で等長でないこと。',
 ]),
 'pag2_part254_full_gluing.md': ('9', [
  '- 前の定理から直ちに出るもの（Lean で確認）：`gaussSum_inv`（Part 5 の `conj_gaussSum` と `chi_neg_one_sq`）。',
  '- 照合者 R4 の判定で数行で出るもの（C）：`rootNum_one_of_eq_one`（Part 192 の `zN_level_one` から。Lean で確認）、`phaseA1_one`（確信度 低）。範囲の中の関係（Part 249・252・253 から）：`ip_add_right`・`ip_smul_right`・`normSq_phaseA1`（B）、`iSup_condPart`・`rootNum_one_prime`・`UA1_charU`（C。`UA1_charU` は低）。',
  '- 鎖に新しいもの：全空間の作用素 UA1 と導手ごとの部分 `condPart`、法を上げる引き戻しとの両立、帰納極限 `Lim` の上の作用素 `Uinf` と内積、族の一意性。',
 ]),
 'pag2_part255_resolution_discrete_limit.md': ('10', [
  '- 前の鎖（Part 248 以前と付録 A）に、このパートの宣言と同じ文・直ちに出る文・数行で出る文は見つからなかった（照合者 R5）。',
  '- 範囲の中の関係（Part 250 から）：`closure_logSet`・`sep_of_inf_unmeasured` は直ちに出る（B）、`exists_near_measured`・`one_le_abs_intCast_sub` は数行（C）。`dense_closure_log_primes`・`exists_padicValRat_eq`・`exists_zpow_near`・`exists_near_of_two_unmeasured` は、Part 250 の (2, 3) の場合や素数 1 つの場合を一般化した形。',
 ]),
 'pag2_part256_gluing_cross_term.md': ('9', [
  '- **このパートの前半は、Part 189・190・195・232 の結果の示し直しだった（Lean で確認）。** PAG193（Part 189）は PAG260 の import の閉包に入っていて、使える状態だった。',
  '  - 同じ定義・同じ値：`prodChar` は Part 195 の `cmul`・Part 232 の `charMul` と同じ定義（同じ対象の 3 つ目の名前）、`crtMap` は Part 189 の `param` と同じ式、`crossSign` は Part 194 の `rs` と同じ値。',
  '  - 同じ文：`gaussSum_prodChar`（Part 189 の `gaussSum_mul_coprime`）、`isPrimitive_prodChar`（Part 190 の `isPrimitive_mul`、Part 232 の `isPrimitive_charMul`）、`prodChar_apply`（Part 189・195・232）、`crtMap_bijective`・`stdAddChar_crtMap`（Part 189）。',
  '  - 直ちに出る：`cast_crtMap_fst`・`cast_crtMap_snd`（Part 189 の `param_cast₁`・`param_cast₂`）、`charU_prodChar`（Part 232 の `charMul_apply_unit`）、`prodChar_neg_one`（Part 200 の `changeLevel_neg_one`）。',
  '- 照合者 R5 の判定で数行で出るもの（C）：`norm_char_unit`・`norm_cross`・`parFac_prodChar`（`parFac_prodChar` は Part 194 の `gs_combine` と同じ形）。`rootNum_prodChar` は照合者の判定で D（数行との境目）。中身は Part 189 の定理に偶奇の因子のずれを足したもの。',
  '- §1 で「Lean にしていない」とした (i)「法 M·N のすべての指標が積の形に一意に書けること」は、鎖には Part 190 の `decomp` と Part 232 の `charMul_injective`・`primEquiv`（Prim(m) × Prim(n) ≅ Prim(mn)）としてあった。',
  '- 相互法則：`cross_eq_sign_of_rootNum_one` で「3 つの仮定は外から入れる」とした仮定は、実原始指標では Part 194 の `gauss_sign_real` から成り立つ。相互法則そのものは Part 194 の `real_reciprocity` で、仮定なしに示してある（ガウスの符号決定と同時の帰納法）。着手前の盲検が挙げた循環の危険への答えも、Part 194 にあった。',
  '- §1 の位置づけの「Mathlib と Isabelle AFP に見つかりませんでした」は外の形式化についての記録で、自分の鎖には同じ文があった。着手前の文書（`pag2_part256_preregistration.md`）の「形式化としては新しい可能性があります」は誤りだった。',
  '- 鎖に新しいもの：UA1・phaseA1 の形の式（`phaseA1_prodChar`・`UA1_charU_prodChar`）、例（`rootNum_prodChar_ne_mul`・`rootNum_prodChar_eq_neg_mul`・`phaseA1_prodChar_ne_mul`）、一般の指標での条件つきの文（`cross_eq_sign_of_rootNum_one`）。',
 ]),
}
INLINE = {
 'pag2_part256_gluing_cross_term.md': [
  ('Lean にしていないのは、(i) 法 M·N のすべての指標が積の形に一意に書けること、',
   'Lean にしていないのは、(i) 法 M·N のすべての指標が積の形に一意に書けること（このパートでは。鎖には Part 190・232 にある。§9）、'),
  ('形式化としては、互いに素な法でのガウス和の乗法性は Mathlib と Isabelle AFP に見つかりませんでした（着手前の盲検と、この環境の Mathlib の grep。見落としの可能性あり）。',
   '形式化としては、互いに素な法でのガウス和の乗法性は Mathlib と Isabelle AFP に見つかりませんでした（着手前の盲検と、この環境の Mathlib の grep。見落としの可能性あり）。ただし自分の鎖には Part 189（PAG193）の `gaussSum_mul_coprime` として同じ文がありました（内部照合 2026-11-14、§9）。'),
 ],
 'pag2_part252_hartley_gluing.md': [
  ('  - 盲検の問いテストは済んでいます（同じ文書の §6 の S1：標準的な演習、Hartley の形の文献は見つからず）。',
   '  - 盲検の問いテストは済んでいます（同じ文書の §6 の S1：標準的な演習、Hartley の形の文献は見つからず）。自分の鎖には付録 A の Part 3（PAG3.lean）の命題 2.8 があった（内部照合 2026-11-14、§9）。'),
 ],
}
def run():
    for fn, (num, body) in SEC.items():
        p = f'{D}/{fn}'
        s = open(p, encoding='utf-8').read()
        if '内部照合（2026-11-14' in s and f'## {num}. 内部照合' in s:
            print(fn, 'already'); continue
        for a, b in INLINE.get(fn, []):
            assert s.count(a) == 1, (fn, a[:30])
            s = s.replace(a, b)
        s = s.rstrip('\n') + f'\n\n## {num}. 内部照合（2026-11-14、{REP}）\n\n' + '\n'.join(body + [LIM]) + '\n'
        open(p, 'w', encoding='utf-8').write(s)
        print(fn, 'section', num, 'added')
    # Part 256 の着手前の文書の訂正
    p = f'{D}/pag2_part256_preregistration.md'
    s = open(p, encoding='utf-8').read()
    if '訂正（2026-11-14' not in s:
        s = s.rstrip('\n') + ('\n\n## 訂正（2026-11-14、内部照合）\n\n'
             '- 結論の「形式化としては新しい可能性があります」は誤りでした。互いに素な法でのガウス和の乗法性は、Part 189（PAG193）の '
             '`gaussSum_mul_coprime` として自分の鎖にありました。Part 256 はそれを使わずに示し直しました。'
             '詳細は `pag2_internal_audit_249_256.md` と `pag2_part256_gluing_cross_term.md` の §9。\n')
        open(p, 'w', encoding='utf-8').write(s)
        print('prereg256 correction added')
run()
