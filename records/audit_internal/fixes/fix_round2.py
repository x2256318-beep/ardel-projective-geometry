# 直しの照合 F（2026-11-14）の指摘を受けた 2 回目の直し。Lean（docstring と冒頭の説明だけ）・ノート・報告・引き継ぎ・着手前の文書。
import re
LEAN = '/home/claude/leanwork/pagpkg'
N185 = '/home/claude/out185'
def edit(path, pairs):
    s = open(path, encoding='utf-8').read()
    for a, b in pairs:
        c = s.count(a)
        assert c == 1, (path, c, a[:60])
        s = s.replace(a, b)
    open(path, 'w', encoding='utf-8').write(s)
    print('edited', path.split('/')[-1], len(pairs))
def replace_block(path, start, end, new):
    s = open(path, encoding='utf-8').read()
    i = s.index(start); j = s.index(end, i)
    s = s[:i] + new + s[j:]
    open(path, 'w', encoding='utf-8').write(s)
    print('block', path.split('/')[-1])

# ---------- Lean ----------
replace_block(f'{LEAN}/PAG255.lean', '内部照合（2026-11-14、', '\n-/',
 '内部照合（2026-11-14、`pag2_internal_audit_249_256.md`）：`units_eq_of_coprime_parts` は Part 192（PAG196）の `crt_unique` から\n'
 '数行で出る（照合者の判定 C。Lean で確認）。範囲の中では、`kUnit_congr` が Part 249 の `kUnit_mul_natCast` から数行（照合者の判定）。\n'
 'そのほかの主な文は、前の鎖（PAG.lean〜PAG252.lean と PAG3・PAG5・PAG6）に見つからなかった（網羅ではない）。')
replace_block(f'{LEAN}/PAG256.lean', '内部照合（2026-11-14、', '\n-/',
 '内部照合（2026-11-14、`pag2_internal_audit_249_256.md`）：前の鎖と同じ文・同じ値の定義（A。Lean で確認）は、\n'
 '`inv_apply_neg_one`・`neg_one_mul_self`（Part 5・21・25・77）、`isPrimitive_of_prime_of_ne_one`（Part 167）、`casKer`（付録 A の\n'
 'Part 3 の `casK` と同じ値）。前の宣言から直ちに出るもの（B。Lean で確認）は、`rootNum`（Part 192 の `zN` ÷ Part 194 の `gs` と同じ値）、\n'
 '`inv_apply_units_inv`・`sum_mul_stdAddChar_neg`（付録 A の Part 3）。照合者の判定で数行で出るもの（C）は、`hartley_one`・`casKer_eq`\n'
 '（付録 A の Part 3 の命題 2.8 `hartley_char`、`casK_even_part`・`casK_odd_part` から。この 2 件は Lean で確認）、`hartley_eq_of_isPrimitive`・\n'
 '`hartley_eq_zero_of_not_isUnit`・`hartley_units_inv`・`JH_eq_rootNum_mul`・`JH_eq_rootNum_mul_any`（`hartley_char` などから。5 件とも\n'
 '確信度 低、Lean では未確認）、`normSq_rootNum`（Part 12 の `normSq_gaussSum` から。Lean で確認）、`exists_primitive_odd_three`\n'
 '（Part 115・163・167 から。Lean で確認）・`exists_primitive_even_five`、`parFac`・`rootNum_eq`（Part 194 の `gs`、付録 A の Part 2 の\n'
 '`parity_weight`）。前の鎖に見つからなかったもの（網羅ではない）は、変換としての定義（`hartley`・`JH`）と、反例（`removal_counterexample` など）。')
edit(f'{LEAN}/PAG256.lean', [('/-- |W(χ)|² = 1（χ 原始的。Part 16 の |τ(χ)|² = N から）。 -/',
                              '/-- |W(χ)|² = 1（χ 原始的。Part 12（PAG16）の |τ(χ)|² = N から）。 -/')])
replace_block(f'{LEAN}/PAG257.lean', '内部照合（2026-11-14、', '\n-/',
 '内部照合（2026-11-14、`pag2_internal_audit_249_256.md`）：`charU` は Part 1 の `PAG.charFun` に `MulChar.toUnitHom` を通したものと\n'
 '同じ関数、`ip` は Part 249 の `ipG` と同じ定義（範囲の中）。`eq_one_of_two`（Part 194）、`not_isPrimitive_one_of_two_le`・\n'
 '`charU_one_mem_Vimprim`（Part 191）、`not_isPrimitive_one_prime`（Part 28）、`Vprim_two`（Part 26）は前の定理から直ちに出る（Lean で確認）。\n'
 '照合者の判定では `ip_charU`（Part 214 の `sum_units_char` と付録 A の Part 3 の `conj_apply_eq_inv`）も数行で出る（Lean では未確認）。\n'
 '作用素 T と V_prim の上のユニタリ性などの主な文は、前の鎖に見つからなかった（網羅ではない）。')
edit(f'{LEAN}/PAG257.lean', [('（Part 218 の `sum_units_char` から）。 -/', '（Part 214（PAG218）の `sum_units_char` から）。 -/')])
replace_block(f'{LEAN}/PAG258.lean', '内部照合（2026-11-14、', '\n',  # 1 行目だけ置き換えて、続きは下で
 '内部照合（2026-11-14、`pag2_internal_audit_249_256.md`）：`gaussSum_inv` は Part 5（PAG9）の `conj_gaussSum` と `chi_neg_one_sq` から')
edit(f'{LEAN}/PAG258.lean', [('（Lean で確認）。照合者の判定では `rootNum_one_of_eq_one`（Part 192 の `zN_level_one` から。Lean で確認）と `phaseA1_one` も数行。',
                              '（Lean で確認）。照合者の判定では `rootNum_one_of_eq_one`（Part 192 の `zN_level_one` から。Lean で確認）と `phaseA1_one`（確信度 低）も数行。'),
                             ('直極限、作用素 Uinf と UA1 の一意性などの主な文は、前の鎖に見つからなかった。',
                              '直極限、作用素 Uinf と UA1 の一意性などの主な文は、前の鎖に見つからなかった（網羅ではない）。')])
replace_block(f'{LEAN}/PAG260.lean', '内部照合（2026-11-14、', '\n-/',
 '内部照合（2026-11-14、`pag2_internal_audit_249_256.md`）：前の鎖と同じ文・同じ定義（A。Lean で確認）は、`prodChar`（Part 195 の `cmul`・\n'
 'Part 232 の `charMul` と同じ定義）、`crtMap`（Part 189 の `param` と同じ式）、`crossSign`（Part 194 の `rs` と同じ値）、`crtMap_bijective`・\n'
 '`stdAddChar_crtMap`・`gaussSum_prodChar`・`prodChar_apply`（Part 189 の定理と同じ文）、`isPrimitive_prodChar`（Part 190・232 の定理と同じ文）。\n'
 '前の宣言から直ちに出るもの（B。Lean で確認）は、`cast_crtMap_fst`・`cast_crtMap_snd`（Part 189）、`charU_prodChar`（Part 232）、\n'
 '`prodChar_neg_one`（Part 200）。つまり上の 1・2・3 と 6 の前半（`isPrimitive_prodChar`）の宣言は、すべて前の鎖にあった。\n'
 '照合者の判定では、`norm_char_unit`・`norm_cross`・`parFac_prodChar`（4。Part 194 の `gs_combine` と同じ形）は数行で出る（C。Lean では\n'
 '未確認）。`rootNum_prodChar`（5）は照合者の判定で D（C との境目）で、中身は Part 189 の `z_mul_coprime`・`gaussSum_mul_coprime` に\n'
 '偶奇の因子のずれを足したもの（監査者の見立ては C 寄り。Lean ではつないでいない）。「法 M·N のすべての指標が積の形に一意に書けること」は、\n'
 'Part 190 の `decomp`（存在）と Part 232 の `charMul_injective`（一意性）を合わせると出る（監査者の読み。Lean ではつないでいない）。\n'
 '8 の相互法則は、Part 194 の `real_reciprocity` で、W = 1 の仮定を使わずに（互いに素・原始・実の指標のもとで）示してある。\n'
 '前の鎖に見つからなかったもの（網羅ではない）は、UA1・phaseA1 の形の式（6 の後半）、例（7）、一般の指標での条件つきの文（8）。')
edit(f'{LEAN}/PAG260.lean', [
 ('内部照合（2026-11-14）：中身は Part 189（PAG193）の `gaussSum_mul_coprime`（この Part の `gaussSum_prodChar` と同じ文）に、偶奇の因子のずれ（Part 194 の `gs_combine` と同じ形）を足したもの。',
  '内部照合（2026-11-14）：中身は Part 189（PAG193）の `z_mul_coprime`・`gaussSum_mul_coprime`（後者はこの Part の `gaussSum_prodChar` と同じ文）に、偶奇の因子のずれ（Part 194 の `gs_combine` と同じ形）を足したもの（照合者の判定は D で C との境目。Lean ではつないでいない）。'),
 ('内部照合（2026-11-14）：実原始指標では、3 つの仮定は Part 194（PAG198）の `gauss_sign_real` から成り立ち、結論は Part 194 の `real_reciprocity` と同じ式になる（数学として。Lean ではつないでいない）。相互法則そのものは Part 194 で、仮定なしに示してある。',
  '内部照合（2026-11-14）：実原始指標では、3 つの仮定は Part 194（PAG198）の `gauss_sign_real` から成り立ち、結論は Part 194 の `real_reciprocity` の式と同値になる（`crossSign` と `rs` が同じ値なので。数学として。Lean ではつないでいない）。相互法則そのものは Part 194 で、W = 1 の仮定を使わずに（互いに素・原始・実の指標のもとで）示してある。'),
])
# （追記）PAG258 の冒頭 1 行目の「直ちに出る」を戻した（置き換えの範囲を 1 行目全体にしたため抜けた）。fix_round2 の直後に手で直した。
