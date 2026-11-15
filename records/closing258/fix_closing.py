"""閉鎖条件の照合（R2・R3）の指摘による直し。形式文は変えない。"""
import re, openpyxl
def apply(p, reps):
    s = open(p, encoding='utf-8').read()
    for a, b in reps:
        assert s.count(a) == 1, (p, s.count(a), a[:60]); s = s.replace(a, b)
    open(p, 'w', encoding='utf-8').write(s)
PREF = re.compile(r'(?<!最初の形式化の)(?<!最初の形式化の )\s?Part ([123])（PAG([23]?)\.lean')
def gen(s):
    s = PREF.sub(lambda m: '最初の形式化の Part ' + m.group(1) + '（PAG' + m.group(2) + '.lean', s)
    s = re.sub(r'([、。（はで]) +(最初の形式化の Part)', r'\1\2', s)
    s = re.sub(r'(?m)^ +(の `casK`)', r'\1', s)
    return s
def gen_file(p):
    s = open(p, encoding='utf-8').read(); t = gen(s)
    if t != s: open(p, 'w', encoding='utf-8').write(t)
    return s.count('Part'), t.count('最初の形式化の Part')
L = '/home/claude/leanwork/pagpkg/'; N = '/home/claude/out185/'
R = N + 'pag2_internal_audit_249_256.md'
# R3 の個別の直し（先に）
apply(R, [
 ('6 件を標本として Lean で確かめ、6 件とも判定どおりでした。', '6 件を標本として Lean で確かめ、6 件とも前の宣言から示せました（`hartley_one` は約 20 行で、C と D の境目）。'),
 ('2 回目の直しは照合者 F2 が確かめ、F2 の指摘への対応は記録だけで直しました（照合は受けていない。§8）。', '2 回目の直しは照合者 F2 が確かめました。F2 の指摘への対応（3 回目の直し）は、Part 258 の閉鎖条件 3 の照合（照合者 R3、§9）を受けました。'),
 ('- いずれも rc 0 です。64 定理すべてに `#print axioms` を付け、', '- いずれも rc 0 です。64 定理すべてに（あとで足した `MechChecksA.lean` の 28 定理も合わせて 92 定理に）`#print axioms` を付け、'),
 ('Part 252 の χ(−1) の補題 3 つ、', 'Part 252 の χ(−1) の補題 2 つと `isPrimitive_of_prime_of_ne_one`、'),
 ('xlsx では、これらのファイルの定理は本文の定理 2.6・4.5、命題 2.8 と付録 A.2 の注記で、「付録 A」は一部だけです。F2 の後に「Part n（PAGn.lean）」に直しました。',
  'xlsx では、これらのファイルの定理は本文の定理 2.6・4.5、命題 2.8 と付録 A.2 の注記などで、「付録 A」は一部だけです。F2 の後に「Part n（PAGn.lean）」に直し、閉鎖条件 3 の照合（R3）の指摘で「最初の形式化の Part n（PAGn.lean）」にそろえました（PAG 2.0 の Part n ＝ PAG(n+4) と区別するため）。'),
 ('どれも照合者の判定として記録したもので、Lean の根拠は主張していません。', '`ipG_smul_left`・`ipG_smul_right` の 2 定理（Lean で確認）を除き、照合者の判定として記録したもので、Lean の根拠は主張していません。'),
 ('xlsx ではこれらの定理は本文の定理 2.6・4.5、命題 2.8 と付録 A.2 の注記で、「付録 A」は一部だけでした。', 'xlsx ではこれらの定理は本文の定理 2.6・4.5、命題 2.8 と付録 A.2 の注記などで、「付録 A」は一部だけでした。'),
])
apply(N + 'pag2_part253_primitive_operator.md', [('`charU` は基本ファイル（Part 1）の `PAG.charFun`', '`charU` は最初の形式化の Part 1（PAG.lean）の `PAG.charFun`')])
# R2 の直し
apply(N + 'pag2_part255_resolution_discrete_limit.md', [
 ('照合 B4 で、A2 の引用（36 行）以外は「入った」と判定された。B4 の後に、36 行の引用を A2 の原文どおりにして出所を書き、158 行の重複を消し、この行を足した（照合を受けていない）。',
  '照合 B4 では、36 行の A2 の引用が不十分、158 行は「根拠は足されたが重複、結論の当否は判定できない」、Ξ3 の記録漏れと 38 行が §9 にないことの指摘があり、ほかは「入った」と判定された（閉鎖条件 2 の照合 R2 の指摘で、「36 行以外は入った」から書き直した）。B4 の後に、36 行の引用を A2 の原文どおりにして出所を書き、158 行の重複を消し、この行と次の「A2 が挙げたコメント」の行を足した（この直しは Part 258 の閉鎖条件 2 の照合 R2 を受けた）。'),
])
apply(N + 'pag2_part252_hartley_gluing.md', [
 ('- **B2。** 形式文 22 個に偽・別物はなく、全体として空虚でもない（注意：原始性を仮定する 4 文は N = 2 では空虚に成り立つ。法 2 に原始指標がないことは Lean の外。',
  '- **B2。** 形式文 22 個に偽・別物はない（B2 の判定。注意：原始性を仮定する 4 文は N = 2 では空虚に成り立つ。以下は構築者の注記：全体として空虚ではない。法 2 に原始指標がないことは Lean の外。'),
])
apply(N + 'pag2_part254_full_gluing.md', [
 ('照合 B4 で「入った」と判定された。B4 の後に題の「法 M の」とこの行だけを足した（照合を受けていない）。',
  '照合 B4 でおおむね「入った」と判定された（§8 の A2 の要約は「入った（中）」で、`iSupIndep_condPart` が境目かは B4 は確かめられないとした。§1 への追記は入れていない）。B4 の後に題の「法 M の」とこの行だけを足した（この直しは Part 258 の閉鎖条件 2 の照合 R2 を受けた）。'),
])
apply(L + 'PAG260.lean', [('ガウス和と W の式では外しても成り立つ（外した形は Lean にしていない）', 'ガウス和と W の式では外しても（両辺 0 で）成り立つ（外した形は Lean にしていない）')])
s = open(L + 'PAG260.lean', encoding='utf-8').read()
import sys
# 「（両辺 0）」の重複を消す
if '（外した形は Lean にしていない）\n（両辺 0）' in s:
    s = s.replace('（外した形は Lean にしていない）\n（両辺 0）が、仮定つきのまま。', '（外した形は Lean にしていない）\nが、仮定つきのまま。')
open(L + 'PAG260.lean', 'w', encoding='utf-8').write(s)
# 書き方をそろえる（R3 の 2・8）
files = [L + f'PAG{n}.lean' for n in (255, 256, 257, 258, 259, 260, 261)]
files += [N + f for f in ['pag2_internal_audit_249_256.md', 'pag2_part249_idele_class_density.md', 'pag2_part250_resolution_emergence.md', 'pag2_part251_projective_limit.md',
          'pag2_part252_hartley_gluing.md', 'pag2_part253_primitive_operator.md', 'pag2_part254_full_gluing.md', 'pag2_part255_resolution_discrete_limit.md',
          'pag2_part256_gluing_cross_term.md', 'pag2_part256_preregistration.md', 'pag2_part257_preregistration.md']]
files += ['/home/claude/out/final78/PAG2_handoff_part257.md', '/home/claude/out/audit_internal/rule_proposal_internal_check.md']
for f in files: print(f.split('/')[-1], gen_file(f))
# 引き継ぎメモ：すべて当たり、番号の規則
H = '/home/claude/out/final78/PAG2_handoff_part257.md'
s = open(H, encoding='utf-8').read()
s = s.replace('C の判定から 6 件を標本として Lean で確かめた（`SampleC2.lean`、すべて当たり）', 'C の判定から 6 件を標本として Lean で確かめた（`SampleC2.lean`、6 件とも前の宣言から示せた。`hartley_one` は約 20 行で C と D の境目）')
old = '「付録 A」とまとめて呼ばない）。'
if old in s and '書くときは「最初の形式化の Part n（PAGn.lean）」' not in s:
    s = s.replace(old, old + ' 書くときは「最初の形式化の Part n（PAGn.lean）」とし、PAG 2.0 の Part n（PAG(n+4).lean）と区別する（2026-11-14、閉鎖条件 3 の照合 R3 の指摘）。', 1)
open(H, 'w', encoding='utf-8').write(s)
# xlsx
X = '/home/claude/out/final78/lean_verification_status.xlsx'
wb = openpyxl.load_workbook(X); n = 0
for ws in wb.worksheets:
    for row in ws.iter_rows():
        for c in row:
            if isinstance(c.value, str) and not c.value.startswith('='):
                t = gen(c.value)
                if t != c.value: c.value = t; n += 1
wb.save(X); print('xlsx cells', n)
