# 内部照合（2026-11-14）の結果を Lean の docstring と冒頭に書き足す。文（statement）は変えない。
import re, shutil, os, sys
SRC = '/home/claude/leanwork/pagpkg'
BK = '/home/claude/out/audit_internal/before_fixes'
TAG = '内部照合（2026-11-14）：'
DOC = {
 'PAG256': {
  'inv_apply_neg_one': 'Part 5（PAG9）の `inv_apply_neg_one`、Part 21（PAG25）の `chi_inv_neg_one`、Part 77（PAG81）の `inv_neg_one` と同じ文（Lean で両向きに確認）。',
  'isPrimitive_of_prime_of_ne_one': 'Part 167（PAG171）の `primitive_of_ne_one` と同じ文（Lean で両向きに確認）。',
  'neg_one_mul_self': 'Part 5（PAG9）の `chi_neg_one_sq`、Part 25（PAG29）の `chi_neg_one_sq\'` と同じ文（Lean で両向きに確認）。',
  'casKer': '付録 A の Part 3（PAG3.lean）の `casK` と同じ値（式の書き方は違う。Lean で値の一致を確認）。',
  'rootNum': 'Part 192（PAG196）の `zN` を Part 194（PAG198）の `gs` で割ったものと同じ値（Lean で確認）。',
  'inv_apply_units_inv': '付録 A の Part 3（PAG3.lean）の `apply_inv_eq_inv_apply` から 1 行で出る（Lean で確認）。',
  'sum_mul_stdAddChar_neg': '付録 A の Part 3（PAG3.lean）の `sum_neg_twist` の x = 1 の場合（Lean で確認）。',
 },
 'PAG257': {
  'charU': '基本ファイル（PAG.lean、Part 1）の `PAG.charFun` に `MulChar.toUnitHom` を通したものと同じ関数（Lean で確認）。',
  'ip': 'Part 249（PAG253）の `ipG` の G = (ZMod N)ˣ の場合と定義上同じ（`rfl` で確認）。',
  'eq_one_of_two': 'Part 194（PAG198）の `level_two_trivial` から直ちに出る（Lean で確認）。',
  'not_isPrimitive_one_of_two_le': 'Part 191（PAG195）の `ne_one_of_isPrimitive` の対偶（Lean で確認）。',
  'charU_one_mem_Vimprim': 'Part 191（PAG195）の `ne_one_of_isPrimitive` から 1 行（Lean で確認）。',
  'not_isPrimitive_one_prime': 'Part 28（PAG32）の `prim_level_p_iff` から 1 行（Lean で確認）。',
  'Vprim_two': 'Part 26（PAG30）の `no_prim_mod_two` から出る（張る集合が空。Lean で確認）。',
 },
 'PAG258': {
  'gaussSum_inv': 'Part 5（PAG9）の `conj_gaussSum` と `chi_neg_one_sq` から 1 行（Lean で確認）。',
 },
 'PAG260': {
  'prodChar': 'Part 195（PAG199）の `cmul`、Part 232（PAG236）の `charMul` と同じ定義（Lean で `HEq` の `rfl` を確認）。同じ対象の 3 つ目の名前。',
  'crtMap': 'Part 189（PAG193）の `param` と同じ式（Lean で `rfl` を確認）。',
  'cast_crtMap_fst': 'Part 189（PAG193）の `param_cast₁` から直ちに出る（Lean で確認）。',
  'cast_crtMap_snd': 'Part 189（PAG193）の `param_cast₂` から直ちに出る（Lean で確認）。',
  'crtMap_bijective': 'Part 189（PAG193）の `param_bijective` と同じ文（Lean で両向きに確認）。',
  'stdAddChar_crtMap': 'Part 189（PAG193）の `stdAddChar_param` と同じ文（Lean で両向きに確認）。',
  'prodChar_apply': 'Part 189（PAG193）の `mul_changeLevel_apply`、Part 195（PAG199）の `cmul_apply`、Part 232（PAG236）の `charMul_apply` と同じ文（Lean で両向きに確認）。',
  'gaussSum_prodChar': 'Part 189（PAG193）の `gaussSum_mul_coprime` と同じ文（Lean で両向きに確認）。この Part はそれを使わずに示し直していた。',
  'prodChar_neg_one': 'Part 200（PAG204）の `changeLevel_neg_one` を 2 回使うだけ（Lean で確認）。',
  'crossSign': 'Part 194（PAG198）の `rs` と同じ値（式は違う。χ(−1) = ±1 による。Lean で確認）。',
  'rootNum_prodChar': '中身は Part 189（PAG193）の `gaussSum_mul_coprime`（この Part の `gaussSum_prodChar` と同じ文）に、偶奇の因子のずれ（Part 194 の `gs_combine` と同じ形）を足したもの。',
  'isPrimitive_prodChar': 'Part 190（PAG194）の `isPrimitive_mul`、Part 232（PAG236）の `isPrimitive_charMul` と同じ文（Lean で両向きに確認）。',
  'cross_eq_sign_of_rootNum_one': '実原始指標では、3 つの仮定は Part 194（PAG198）の `gauss_sign_real` から成り立ち、結論は Part 194 の `real_reciprocity` と同じ式になる（数学として。Lean ではつないでいない）。相互法則そのものは Part 194 で、仮定なしに示してある。',
  'charU_prodChar': 'Part 232（PAG236）の `charMul_apply_unit` から直ちに出る（Lean で確認）。',
 },
}
HEAD = {
 'PAG255': ['内部照合（2026-11-14、`pag2_internal_audit_249_256.md`）：`units_eq_of_coprime_parts` は Part 192（PAG196）の `crt_unique` から',
            '数行で出る（照合者の判定。Lean で確認）。そのほかの主な文は、前の鎖（PAG.lean〜PAG254.lean と PAG3・PAG5・PAG6）に見つからなかった。'],
 'PAG256': ['内部照合（2026-11-14、`pag2_internal_audit_249_256.md`）：次の宣言は前の鎖に同じ文・同じ値の定義がある（Lean で確認）。',
            '`inv_apply_neg_one`・`neg_one_mul_self`（Part 5・21・25・77）、`isPrimitive_of_prime_of_ne_one`（Part 167）、`casKer`（付録 A の',
            'Part 3 の `casK`）、`rootNum`（Part 192 の `zN` ÷ Part 194 の `gs`）、`inv_apply_units_inv`・`sum_mul_stdAddChar_neg`（付録 A の Part 3）。',
            '照合者の判定では、Hartley の部分（`hartley_one`・`hartley_eq_of_isPrimitive`・`hartley_eq_zero_of_not_isUnit`・`hartley_units_inv`・',
            '`JH_eq_rootNum_mul`・`JH_eq_rootNum_mul_any`・`casKer_eq`）は付録 A の Part 3 の命題 2.8（`hartley_char`）から数行で出る。',
            '`normSq_rootNum`（Part 12 の `normSq_gaussSum` から。Lean で確認）、`exists_primitive_odd_three`（Part 115・163・167 から。Lean で確認）・',
            '`exists_primitive_even_five`、`parFac`・`rootNum_eq`（Part 194 の `gs`、付録 A の Part 2 の `parity_weight`）も同様。',
            'このファイルで鎖に新しいのは、変換としての定義（`hartley`・`JH`）と、反例（`removal_counterexample` など）。'],
 'PAG257': ['内部照合（2026-11-14、`pag2_internal_audit_249_256.md`）：`charU`（Part 1 の `PAG.charFun`）と `ip`（Part 249 の `ipG`）は前の定義と',
            '同じ対象。`eq_one_of_two`（Part 194）、`not_isPrimitive_one_of_two_le`・`charU_one_mem_Vimprim`（Part 191）、`not_isPrimitive_one_prime`',
            '（Part 28）、`Vprim_two`（Part 26）は前の定理から直ちに出る（Lean で確認）。照合者の判定では `ip_charU`（Part 214 の `sum_units_char` と',
            '付録 A の Part 3 の `conj_apply_eq_inv`）も数行で出る。作用素 T と V_prim の上のユニタリ性などの主な文は、前の鎖に見つからなかった。'],
 'PAG258': ['内部照合（2026-11-14、`pag2_internal_audit_249_256.md`）：`gaussSum_inv` は Part 5（PAG9）の `conj_gaussSum` から直ちに出る',
            '（Lean で確認）。照合者の判定では `rootNum_one_of_eq_one`（Part 192 の `zN_level_one` から。Lean で確認）と `phaseA1_one` も数行。',
            '直極限、作用素 Uinf と UA1 の一意性などの主な文は、前の鎖に見つからなかった。'],
 'PAG260': ['内部照合（2026-11-14、`pag2_internal_audit_249_256.md`）：上の 1〜3 と 6 の前半は前の鎖にあった。4 は Part 194 の `gs_combine`（偶奇の',
            '因子を逆数で正規化した形）と同じ内容で、5 はそれらから数行（照合者の判定は数行と新しいの境目）。`prodChar` は Part 195 の `cmul`・',
            'Part 232 の `charMul` と同じ定義、`crtMap` は Part 189 の `param` と同じ式、`crossSign` は Part 194 の `rs` と同じ値（Lean で確認）。',
            '`crtMap_bijective`・`stdAddChar_crtMap`・`gaussSum_prodChar`・`prodChar_apply` は Part 189 の定理と同じ文、`isPrimitive_prodChar` は',
            'Part 190・232 の定理と同じ文、`cast_crtMap_fst`・`cast_crtMap_snd`・`charU_prodChar`・`prodChar_neg_one` は Part 189・200・232 の定理から',
            '直ちに出る（Lean で確認）。照合者の判定では `norm_char_unit`・`norm_cross`・`parFac_prodChar`（Part 194 の `gs_combine` と同じ形）も数行。',
            '「法 M·N のすべての指標が積の形に一意に書けること」は、Part 190 の `decomp` と Part 232 の `charMul_injective`・`primEquiv` で鎖にある。',
            '8 の相互法則は、Part 194 の `real_reciprocity` で仮定なしに示してある。このファイルで鎖に新しいのは、UA1・phaseA1 の形の式（6 の後半）、',
            '例（7）、一般の指標での条件つきの文（8）。'],
}
DECL = lambda n: re.compile(r'^(@\[[^\]]*\]\s*)?(noncomputable\s+)?(theorem|lemma|def|abbrev)\s+' + re.escape(n) + r'(\s|$)')
def fix(f):
    path = f'{SRC}/{f}.lean'
    if not os.path.exists(f'{BK}/{f}.lean'):
        shutil.copy(path, f'{BK}/{f}.lean')
    lines = open(path, encoding='utf-8').read().split('\n')
    if any(TAG in l or '内部照合（2026-11-14、' in l for l in lines):
        print(f, 'already fixed; skip'); return
    for name, note in DOC.get(f, {}).items():
        idx = [i for i, l in enumerate(lines) if DECL(name).match(l)]
        assert len(idx) == 1, (f, name, idx)
        j = idx[0] - 1
        while lines[j].startswith('@[') or lines[j].startswith('omit ') or lines[j].startswith('open '):
            j -= 1
        assert lines[j].rstrip().endswith('-/'), (f, name, lines[j])
        last = lines[j].rstrip()
        body = last[:-2].rstrip()
        lines[j:j + 1] = [body, TAG + note + ' -/']
    if f in HEAD:
        k = lines.index('-/')   # 冒頭の注釈の終わり（最初の単独の -/）
        lines[k:k] = [''] + HEAD[f]
    open(path, 'w', encoding='utf-8').write('\n'.join(lines))
    print(f, 'fixed:', len(DOC.get(f, {})), 'docstrings,', 'header' if f in HEAD else 'no header')


if __name__ == '__main__':
    for f in (sys.argv[1:] or ['PAG255', 'PAG256', 'PAG257', 'PAG258', 'PAG260']):
        fix(f)
