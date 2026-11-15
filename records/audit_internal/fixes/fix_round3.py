# F2 の後の直し（記録だけ。照合は受けていない）。(1) 「付録 A」の取り違え：PAG.lean・PAG2・PAG3 は PAG 2.0 より前の最初の形式化の
# Part 1〜3 で、本文の定理 2.6・4.5、命題 2.8 と付録 A.2 の注記などを含む（xlsx の「定理と証明」の見出しによる）。「付録 A の Part n」を
# 「Part n（PAGn.lean）」に直す。(2) 照合者 F2 の新しい指摘への対応。
import re
from openpyxl import load_workbook
GEN = [
 (r'付録 A の Part 3（PAG3\.lean、命題 2\.8 `hartley_char`）', 'Part 3（PAG3.lean。命題 2.8 `hartley_char`）'),
 (r'付録 A の Part 3（PAG3\.lean、命題 2\.8 hartley_char）', 'Part 3（PAG3.lean。命題 2.8 hartley_char）'),
 (r'付録 A の Part 3（PAG3\.lean。鎖に import されていない初めのファイル）', 'Part 3（PAG3.lean。PAG 2.0 より前の最初の形式化のファイルで、鎖に import されていない）'),
 (r'付録 A の Part 3（PAG3\.lean、命題 2\.8）', 'Part 3（PAG3.lean。命題 2.8）'),
 (r'付録 A の Part 3（PAG3\.lean）', 'Part 3（PAG3.lean）'),
 (r'付録 A の\s*\n\s*Part 3', 'Part 3（PAG3.lean）\n'),
 (r'付録 A の Part 3）', 'Part 3（PAG3.lean））'),
 (r'付録 A の Part 3', 'Part 3（PAG3.lean）'),
 (r'付録 A の Part 2 の\s*\n`parity_weight`', 'Part 2（PAG2.lean）の\n`parity_weight`'),
 (r'付録 A の Part 2', 'Part 2（PAG2.lean）'),
 (r'Part 1 の `PAG\.charFun`', 'Part 1（PAG.lean）の `PAG.charFun`'),
 (r'Part 1 の PAG\.charFun', 'Part 1（PAG.lean）の PAG.charFun'),
]
def gen(s):
    for a, b in GEN:
        s = re.sub(a, b, s)
    # 和文の直後に来た「Part n（PAG…）」の前に空白を入れる（置き換えで「付録 A の 」が消えたところ）
    s = re.sub(r'([ぁ-んァ-ヶ一-龠ー、。・])Part ([123])（PAG', r'\1 Part \2（PAG', s)
    # 「（PAGn.lean） の」の余分な空白を取る（もとの「Part 3 の」の空白が残ったところ）
    s = re.sub(r'（PAG([23]?)\.lean） ([ぁ-んァ-ヶ一-龠])', r'（PAG\1.lean）\2', s)
    return s
def edit_text(path, extra=()):
    s = open(path, encoding='utf-8').read()
    s0 = s
    s = gen(s)
    for a, b in extra:
        if b in s and a not in s:
            continue
        c = s.count(a); assert c == 1, (path, c, a[:60])
        s = s.replace(a, b)
    open(path, 'w', encoding='utf-8').write(s)
    print('edited', path.split('/')[-1], 'changed' if s != s0 else 'no change')
LEAN = '/home/claude/leanwork/pagpkg'
N185 = '/home/claude/out185'
edit_text(f'{LEAN}/PAG256.lean')
edit_text(f'{LEAN}/PAG257.lean')
edit_text(f'{LEAN}/PAG260.lean', [
 ('前の鎖と同じ文・同じ定義（A。Lean で確認）は、', '前の鎖と同じ文・同じ値の定義（A。Lean で確認）は、'),
 ('の宣言は、すべて前の鎖にあった。', 'の宣言は、すべて前の鎖にあるか、前の宣言から直ちに出る（A・B）。'),
 ('（`crossSign` と `rs` が同じ値なので。数学として。', '（`crossSign` と `rs` が同じ値で、どちらも ±1 なので。数学として。'),
])
edit_text(f'{N185}/pag2_part249_idele_class_density.md', [
 ('鎖に import されていない付録 A・PAG 2.0 の初めのファイル PAG3・PAG5・PAG6', '鎖に import されていない、最初の形式化の Part 3（PAG3.lean）と PAG 2.0 の初めのファイル PAG5・PAG6'),
])
edit_text(f'{N185}/pag2_part252_hartley_gluing.md', [
 ('鎖の中では Part 3（PAG3.lean）の命題 2.8 の再導出にあたると見る（確信度：中〜高）。', '鎖の中では Part 3（PAG3.lean）の命題 2.8 の再導出にあたると見る（確信度：中。中心 7 件のうち Lean で確かめたのは 2 件で、残り 5 件は照合者の確信度が低いため）。'),
])
edit_text(f'{N185}/pag2_part253_primitive_operator.md')
edit_text(f'{N185}/pag2_part256_gluing_cross_term.md')
edit_text(f'{N185}/pag2_part257_preregistration.md', [
 ('P1 で鎖に新しいのは、', 'P1 で前の鎖に見つからなかったのは（網羅ではない）、'),
])
edit_text('/home/claude/out/audit_internal/rule_proposal_internal_check.md')
# 報告
edit_text(f'{N185}/pag2_internal_audit_249_256.md', [
 ('（Part 3（PAG3.lean）と PAG 2.0 の初め）', '（PAG 2.0 より前の最初の形式化の Part 3 と、PAG 2.0 の初め）'),
 ('PAG.lean・PAG2・PAG3・PAG4 は付録 A の Part 1〜4。', 'PAG.lean・PAG2・PAG3・PAG4 は PAG 2.0 より前の最初の形式化の Part 1〜4（xlsx の検証手順の記載。本文の定理 2.6・4.5、命題 2.8、付録 A.2 の注記などを含む）。'),
 ('- **前の鎖の定義と一致する定義が 7 つありました。**', '- **前の鎖の定義と一致する定義が 6 つ、範囲の中で一致する定義が 1 つありました。**'),
 ('5. **前の鎖に対する A・B を Lean で確かめました。** 直接の当てはめで通った組は、名前つきの定理に書き直しました（`lean/MechChecks.lean`、44 定理）。通らなかった組は、前の宣言だけから手で示しました（`lean/ManualChecks2.lean`、14 件）。',
  '5. **前の鎖に対する A・B を Lean で確かめました。** 直接の当てはめで通った組は、名前つきの定理に書き直しました（`lean/MechChecks.lean`、44 定理。前の鎖に対する 28 組と範囲の中の 2 組で、Part 249 の一般化 5 定理を含む）。通らなかった組は、前の宣言だけから手で示しました（`lean/ManualChecks2.lean`、14 件。うち 1 件は範囲の中の `ip`）。'),
 ('  - `charU` は、照合者の判定（B、推定）より強く、同じ関数でした。', '  - `charU` は、照合者の判定（B、推定）より強く、`PAG.charFun` に `toUnitHom` を通したものと同じ関数でした。'),
 ('鎖の中では Part 3（PAG3.lean）の命題 2.8 の再導出にあたると見ます（確信度：中〜高）。', '鎖の中では Part 3（PAG3.lean）の命題 2.8 の再導出にあたると見ます（確信度：中。中心 7 件のうち Lean で確かめたのは 2 件で、残り 5 件は照合者の確信度が低いため）。'),
 ('- **第 8 の型（規約）**：Part 252・253 の記録に、ファイル番号を Part 番号として書いた取り違えがありました（「Part 16」は正しくは Part 12 = PAG16、「Part 218」は正しくは Part 214 = PAG218）。',
  '- **第 8 の型（規約）**：Part 249・252・253 の記録に、ファイル番号を Part 番号として書いた取り違えがありました（「Part 16」は正しくは Part 12 = PAG16、「Part 218」は正しくは Part 214 = PAG218。Part 249 の行の `dil_one`・`dil_dil` も PAG218 の宣言）。さらに私自身が、PAG.lean・PAG2・PAG3 をまとめて「付録 A」と書いていました。xlsx では、これらのファイルの定理は本文の定理 2.6・4.5、命題 2.8 と付録 A.2 の注記で、「付録 A」は一部だけです。F2 の後に「Part n（PAGn.lean）」に直しました。'),
 ('（`crossSign` と `rs` が同じ値なので。数学として。Lean ではつないでいない）。', '（`crossSign` と `rs` が同じ値で、どちらも ±1 なので。数学として。Lean ではつないでいない）。'),
 ('- **C の標本**（`SampleC2.lean`、6 件）：`normSq_rootNum`、`rootNum_one_of_eq_one`、`units_eq_of_coprime_parts`、`exists_primitive_odd_three`、`hartley_one`、`casKer_eq`。どれも前の宣言から数行で示せました（`hartley_one` は約 20 行で、うち半分は偶奇の場合分け）。',
  '- **C の標本**（`SampleC2.lean`、6 件）：`normSq_rootNum`、`rootNum_one_of_eq_one`、`units_eq_of_coprime_parts`、`exists_primitive_odd_three`、`hartley_one`、`casKer_eq`。標本は無作為ではなく、Lean で確かめやすいものと、主な主張（Hartley の部分、W の正規化）を支えるものを選びました。5 件は 5〜8 行で示せました。`hartley_one` は約 20 行（半分は偶奇の場合分け）で、C と D の境目にあたります。\n- **「同じ文（両向き）」の 14 組は、`simp_all` の分岐を使わずに通ることも確かめました**（`lean/MechChecksA.lean`、28 定理。`exact` か、`apply` と仮定だけ。照合者 F2 の指摘）。'),
])

# 引き継ぎメモ
edit_text('/home/claude/out/final77/PAG2_handoff_internal_audit.md', [
 ('PAG.lean・PAG2・PAG3・PAG4 は付録 A の Part 1〜4。', 'PAG.lean・PAG2・PAG3・PAG4 は PAG 2.0 より前の最初の形式化の Part 1〜4（本文の定理 2.6・4.5、命題 2.8、付録 A.2 の注記などを含む。「付録 A」とまとめて呼ばない）。'),
 ('Part 252・253 の記録に「Part 16」', 'Part 249・252・253 の記録に「Part 16」'),
 ('一方を他方にそのまま当てる確認を約 1 万 3 千組。', '一方を他方にそのまま当てる確認を約 1 万 3 千回（組ごとに両向き）。'),
 ('ManualChecks2.lean`。対象の型そのものを `type_of%` で述べる）', 'ManualChecks2.lean`。定理は対象の型そのものを `type_of%` で述べ、定義の一致は値の等式か `HEq rfl` で確かめる）'),
 ('  - Part 252：A・B が 7（χ(−1) の補題 3 つは Part 5・21・25・77・167 と同じ文、`casKer` は Part 3（PAG3.lean）の `casK` と同じ値、`rootNum` は Part 192 の `zN` ÷ Part 194 の `gs` と同じ値）。',
  '  - Part 252：A が 4（`inv_apply_neg_one`・`neg_one_mul_self` は Part 5・21・25・77 と、`isPrimitive_of_prime_of_ne_one` は Part 167 と同じ文、`casKer` は Part 3（PAG3.lean）の `casK` と同じ値）、B が 3（`rootNum` は Part 192 の `zN` ÷ Part 194 の `gs` と同じ値、`inv_apply_units_inv`・`sum_mul_stdAddChar_neg` は Part 3（PAG3.lean）から 1 行）。'),
])
# xlsx
P = '/home/claude/out/final77/lean_verification_status.xlsx'
wb = load_workbook(P)
n = 0
for ws in wb.worksheets:
    for row in ws.iter_rows(min_row=31):
        for c in row:
            if isinstance(c.value, str) and ('付録 A の Part' in c.value or 'Part 1 の PAG.charFun' in c.value):
                v = gen(c.value)
                if v != c.value: c.value = v; n += 1
ws = wb['定理と証明']
def find_one(pred):
    cs = [ws.cell(r, col) for r in range(2, ws.max_row + 1) for col in (1, 4) if isinstance(ws.cell(r, col).value, str) and pred(ws.cell(r, col).value)]
    return cs
# 新10：Part 256 の見出し
hs = [ws.cell(r, 1) for r in range(2, ws.max_row + 1) if isinstance(ws.cell(r, 1).value, str) and ws.cell(r, 1).value.startswith('PAG2.0-256 ')]
for c in hs:
    a = '相互法則は Part 194 の real_reciprocity で、W = 1 の仮定を使わずに示してある'
    if a in c.value and '（互いに素・原始・実の指標のもとで）' not in c.value:
        c.value = c.value.replace(a, a + '（互いに素・原始・実の指標のもとで）')
# 新11
for c in find_one(lambda v: '（crossSign と rs が同じ値）' in v):
    c.value = c.value.replace('（crossSign と rs が同じ値）', '（crossSign と rs が同じ値で、どちらも ±1）')
# 新12
ws2 = wb['検証手順']
v = ws2.cell(279, 4).value
if '前の鎖と同じ文・同じ対象（A）' in v:
    ws2.cell(279, 4).value = v.replace('前の鎖と同じ文・同じ対象（A）', '前の鎖と同じ文・同じ値の定義（A）')
wb.save(P)
print('xlsx cells with label fix:', n)
