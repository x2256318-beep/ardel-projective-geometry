# 直しの照合 F の指摘を受けた 2 回目の直し（ノート）。
D = '/home/claude/out185'
def edit(fn, pairs):
    p = f'{D}/{fn}'
    s = open(p, encoding='utf-8').read()
    for a, b in pairs:
        c = s.count(a); assert c == 1, (fn, c, a[:60])
        s = s.replace(a, b)
    open(p, 'w', encoding='utf-8').write(s); print('edited', fn, len(pairs))
def block(fn, start, end, new):
    p = f'{D}/{fn}'
    s = open(p, encoding='utf-8').read()
    i = s.index(start); j = s.index(end, i)
    s = s[:i] + new + s[j:]
    open(p, 'w', encoding='utf-8').write(s); print('block', fn)
edit('pag2_part251_projective_limit.md', [
 ('（照合者 R2 の判定 C。Lean で確認：`audit_internal/lean/SampleC.lean`）', '（照合者 R2 の判定 C。Lean で確認：`audit_internal/lean/SampleC2.lean`）'),
 ('- 範囲の中の関係：`kUnit_congr` は Part 249 の `kUnit_mul_natCast` から数行（C）。', '- 範囲の中の関係：`kUnit_congr` は Part 249 の `kUnit_mul_natCast` から数行（照合者の判定 C。Lean では未確認）。'),
 ('`dense_closure_primeGens` など）は、前の鎖に見つからなかった。', '`dense_closure_primeGens` など）は、前の鎖に見つからなかった（網羅ではない）。'),
])
edit('pag2_part252_hartley_gluing.md', [
 ('|W(χ)|² = |ε(χ)|²·|τ(χ)|²/N = 1（Part 16 の |τ(χ)|² = N）。', '|W(χ)|² = |ε(χ)|²·|τ(χ)|²/N = 1（Part 12（PAG16）の |τ(χ)|² = N）。'),
 ('| 同上と Part 16。素数の法のフーリエ版は Benoist 2024 の式 (3.5) |', '| 同上と Part 12（PAG16）。素数の法のフーリエ版は Benoist 2024 の式 (3.5) |'),
])
block('pag2_part252_hartley_gluing.md', '- **Hartley の部分は、付録 A の Part 3（PAG3.lean、命題 2.8）とほぼ重なっていた。**', '- 限界：機械的な候補選び',
 '- **前の鎖と同じ文・同じ値の定義（A。Lean で確認）**：\n'
 '  - `inv_apply_neg_one`：Part 5 の `inv_apply_neg_one`、Part 21 の `chi_inv_neg_one`、Part 77 の `inv_neg_one` と同じ文。\n'
 '  - `neg_one_mul_self`：Part 5 の `chi_neg_one_sq`、Part 25 の `chi_neg_one_sq\'` と同じ文。\n'
 '  - `isPrimitive_of_prime_of_ne_one`：Part 167 の `primitive_of_ne_one` と同じ文。\n'
 '  - `casKer`：付録 A の Part 3（PAG3.lean）の `casK` と同じ値（式の書き方は違う）。\n'
 '- **前の宣言から直ちに出るもの（B。Lean で確認）**：\n'
 '  - `rootNum`：Part 192 の `zN` を Part 194 の `gs` で割ったものと同じ値。\n'
 '  - `inv_apply_units_inv`・`sum_mul_stdAddChar_neg`：付録 A の Part 3 の `apply_inv_eq_inv_apply`・`sum_neg_twist`（x = 1）から 1 行。\n'
 '- **Hartley の部分（照合者 R2 の判定）**：付録 A の Part 3（PAG3.lean。鎖に import されていない初めのファイル）には、`casK`（Hartley の核）、`casK_even_part`・`casK_odd_part`、`sum_neg_twist`、`hartley_char`（Σ_y cas(xy)χ(y) = (偶 1／奇 −i)·Σ_y e(xy/N)χ(y)。xlsx では「命題 2.8」）、`apply_inv_eq_inv_apply` がある。照合者 R2 の判定では、このパートの Hartley の部分の中心の 7 件（`hartley_one`・`hartley_eq_of_isPrimitive`・`hartley_eq_zero_of_not_isUnit`・`hartley_units_inv`・`JH_eq_rootNum_mul`・`JH_eq_rootNum_mul_any`・`casKer_eq`）は、これらから数行で出る（C）。うち `hartley_one` と `casKer_eq` は Lean で確認した（`audit_internal/lean/SampleC2.lean`）。残り 5 件は照合者の確信度が低く、Lean では確かめていない。\n'
 '- **そのほかの C（照合者 R2 の判定）**：`normSq_rootNum`（Part 12 の `normSq_gaussSum` から。Lean で確認）、`exists_primitive_odd_three`（Part 115・163・167 から。Lean で確認）・`exists_primitive_even_five`、`parFac`・`rootNum_eq`（Part 194 の `gs`、付録 A の Part 2 の `parity_weight`）。`parFac_of_even`・`parFac_of_odd` は付録 A の Part 2 の `parity_weight`（r = 1）から [NeZero N] を外した形。\n'
 '- **前の鎖に見つからなかったもの（網羅ではない）**：変換としての定義（`hartley`・`JH`）と、原始性を外したときの反例（`removal_counterexample`・`removal_counterexample_four`・`removal_counterexample_normSq`）。\n'
 '- §1 の位置づけ「既知の事実の書き直し（再導出）」は変わらない。照合者の判定と Lean で確かめた 2 件から、鎖の中では付録 A の Part 3 の命題 2.8 の再導出にあたると見る（確信度：中〜高）。冒頭の「Hartley の形の文献は見つからず」は外の文献についての記録で、自分の鎖には命題 2.8 があった。\n')
edit('pag2_part253_primitive_operator.md', [
 ('原始指標で |τ(χ)|² = N（Part 16・Part 252）と指標の直交性から出ます。', '原始指標で |τ(χ)|² = N（Part 12（PAG16）・Part 252）と指標の直交性から出ます。'),
 ('Part 218 の単数の上の指標の和 `sum_units_char`。', 'Part 214（PAG218）の単数の上の指標の和 `sum_units_char`。'),
 ('Part 218 の `sum_units_char` は鎖に入っています。', 'Part 214（PAG218）の `sum_units_char` は鎖に入っています。'),
 ('- 前の定義と同じ対象：`charU` は基本ファイル（Part 1）の `PAG.charFun` に `MulChar.toUnitHom` を通したもの、`ip` は Part 249 の `ipG` の G = (ZMod N)ˣ の場合（Lean で確認）。このパートはそれらを使わずに定義し直していた。',
  '- 前の定義と同じもの（Lean で確認）：`charU` は基本ファイル（Part 1）の `PAG.charFun` に `MulChar.toUnitHom` を通したものと同じ関数、`ip` は Part 249 の `ipG` の G = (ZMod N)ˣ の場合と同じ定義（範囲の中）。このパートはそれらを使わずに定義し直していた。'),
 ('範囲の中の関係（Part 252 から）：`JHL`・`TopL_charU`・`Vprim_ne_bot_three`・`TopL_charU_one_four`（低）、`ip_smul_smul`・`rootNum_ne_zero`。',
  '範囲の中の関係（Part 249・252 から。照合者の判定、Lean では未確認）：C は `JHL`・`TopL_charU`・`Vprim_ne_bot_three`・`TopL_charU_one_four`（低）、B は `ip_smul_smul`・`rootNum_ne_zero`。'),
 ('- 鎖に新しいもの：単数の上の作用素 T', '- 前の鎖に見つからなかったもの（網羅ではない）：単数の上の作用素 T'),
])
edit('pag2_part254_full_gluing.md', [
 ('範囲の中の関係（Part 249・252・253 から）：`ip_add_right`・`ip_smul_right`・`normSq_phaseA1`（B）、`iSup_condPart`・`rootNum_one_prime`・`UA1_charU`（C。`UA1_charU` は低）。',
  '範囲の中の関係（Part 249・252・253 から。照合者の判定。Lean で確かめたのは `ip_smul_right` だけ）：B は `ip_add_right`・`ip_smul_right`・`normSq_phaseA1`、C は `iSup_condPart`・`rootNum_one_prime`・`UA1_charU`（`UA1_charU` は低）。'),
 ('- 鎖に新しいもの：全空間の作用素 UA1', '- 前の鎖に見つからなかったもの（網羅ではない）：全空間の作用素 UA1'),
])
edit('pag2_part255_resolution_discrete_limit.md', [
 ('- 前の鎖（Part 248 以前と付録 A）に、このパートの宣言と同じ文・直ちに出る文・数行で出る文は見つからなかった（照合者 R5）。',
  '- 前の鎖（PAG.lean〜PAG252.lean と PAG3・PAG5・PAG6）に、このパートの宣言と同じ文・直ちに出る文・数行で出る文は見つからなかった（照合者 R5。網羅ではない）。'),
 ('`exists_near_measured`・`one_le_abs_intCast_sub` は数行（C）。', '`exists_near_measured`・`one_le_abs_intCast_sub` は数行（C）（照合者の判定。Lean では未確認）。'),
])
edit('pag2_part256_gluing_cross_term.md', [
 ('（このパートでは。鎖には Part 190・232 にある。§9）', '（このパートでは。Part 190・232 の 2 つの定理を合わせると出る。§9）'),
 ('- 照合者 R5 の判定で数行で出るもの（C）：`norm_char_unit`・`norm_cross`・`parFac_prodChar`（`parFac_prodChar` は Part 194 の `gs_combine` と同じ形）。`rootNum_prodChar` は照合者の判定で D（数行との境目）。中身は Part 189 の定理に偶奇の因子のずれを足したもの。',
  '- 照合者 R5 の判定で数行で出るもの（C。Lean では未確認）：`norm_char_unit`・`norm_cross`・`parFac_prodChar`（`parFac_prodChar` は Part 194 の `gs_combine` と同じ形）。`rootNum_prodChar` は照合者の判定で D（C との境目）。中身は Part 189 の `z_mul_coprime`・`gaussSum_mul_coprime` に偶奇の因子のずれを足したもの（監査者の見立ては C 寄り。Lean ではつないでいない）。'),
 ('- §1 で「Lean にしていない」とした (i)「法 M·N のすべての指標が積の形に一意に書けること」は、鎖には Part 190 の `decomp` と Part 232 の `charMul_injective`・`primEquiv`（Prim(m) × Prim(n) ≅ Prim(mn)）としてあった。',
  '- §1 で「Lean にしていない」とした (i)「法 M·N のすべての指標が積の形に一意に書けること」は、Part 190 の `decomp`（存在）と Part 232 の `charMul_injective`（一意性）を合わせると出る（監査者の読み。Lean ではつないでいない）。原始指標については、Part 232 の `primEquiv` が Prim(m) × Prim(n) ≅ Prim(mn) を与える。'),
 ('- 相互法則：`cross_eq_sign_of_rootNum_one` で「3 つの仮定は外から入れる」とした仮定は、実原始指標では Part 194 の `gauss_sign_real` から成り立つ。相互法則そのものは Part 194 の `real_reciprocity` で、仮定なしに示してある（ガウスの符号決定と同時の帰納法）。着手前の盲検が挙げた循環の危険への答えも、Part 194 にあった。',
  '- 相互法則：`cross_eq_sign_of_rootNum_one` で「3 つの仮定は外から入れる」とした仮定は、実原始指標では Part 194 の `gauss_sign_real` から成り立つ（数学として。Lean ではつないでいない）。相互法則そのものは Part 194 の `real_reciprocity` で、W = 1 の仮定を使わずに（互いに素・原始・実の指標のもとで）示してある。xlsx の Part 194 の `gauss_sign_aux` の行によれば、ガウスの符号決定と、素数冪の実原始指標との相互法則を、N についての強い帰納法で同時に示している。着手前の盲検が挙げた循環の危険には、この形で答えている（証明の中身は確かめていない）。'),
 ('- 鎖に新しいもの：UA1・phaseA1 の形の式', '- 前の鎖に見つからなかったもの（網羅ではない）：UA1・phaseA1 の形の式'),
])
