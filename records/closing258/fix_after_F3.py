"""F3 の指摘による最後の直し（記録だけ。照合はここで止める）。形式文は変えない。"""
def apply(p, reps):
    s = open(p, encoding='utf-8').read()
    for a, b in reps:
        assert s.count(a) == 1, (p, s.count(a), a[:60]); s = s.replace(a, b)
    open(p, 'w', encoding='utf-8').write(s)
N = '/home/claude/out185/'; L = '/home/claude/leanwork/pagpkg/'
apply(N + 'pag2_internal_audit_249_256.md', [
 ('- **F2 の後の直し（記録だけ。照合は受けていない）**：', '- **F2 の後の直し（3 回目。Part 258 の閉鎖条件 3 の照合 R3 を受けた。§9）**：'),
 ('PAG.lean（最初の形式化の Part 1）〜PAG252.lean', '最初の形式化の Part 1（PAG.lean）〜PAG252.lean'),
 ('- **判定：新 1〜16 のうち 8 件が直り、6 件は一部、2 件は材料不足で確かめられない（xlsx の差分を渡していなかった）。形式文の変更はない（見た差分の範囲で）。**',
  '- **判定：新 1〜16 のうち 8 件が直り、6 件は一部、2 件は材料不足で確かめられない（新 10 は xlsx の差分を、新 15 は `MechChecksA.lean` とその出力を渡していなかった）。形式文の変更はない（見た差分の範囲で）。** R3 の §2 の 9（「記録だけで直した」の言い方）は直した。10（「付録 A」の残り）は、構築者が全文を検索して、取り違えを説明する文と「付録 A.2」のほかに残りがないことを確かめた（2026-11-14 夜）。'),
 ('  - 「64 定理」が `MechChecksA.lean` の 28 定理の分だけ古い → 92 定理と書いた。',
  '  - 「64 定理」が `MechChecksA.lean` の 28 定理の分だけ古い → 92 定理と書いた。MechChecksA を含む 4 ファイル（MechChecks 44・MechChecksA 28・ManualChecks2 14・SampleC2 6）の .out の `#print axioms` 92 行を数え、公理が propext・Classical.choice・Quot.sound の範囲だけであることを確かめた（`audit_internal/lean/*.out`、2026-11-14 18:4x）。'),
])
apply(N + 'pag2_part252_hartley_gluing.md', [
 ('最初の形式化の Part 3（PAG3.lean。PAG 2.0 より前の最初の形式化のファイルで、鎖に import されていない）', '最初の形式化の Part 3（PAG3.lean。PAG 2.0 より前のファイルで、鎖に import されていない）'),
 ('（B2 の判定。注意：原始性を仮定する 4 文は N = 2 では空虚に成り立つ。以下は構築者の注記：全体として空虚ではない。法 2 に原始指標がないことは Lean の外。`JH_eq_rootNum_mul` は `JH_eq_rootNum_mul_any` に含まれる。`removal_counterexample_four` の第 1 成分はほかの成分と無関係な証人）。',
  '（B2 の判定。注意：原始性を仮定する 4 文は N = 2 では空虚に成り立つ。`JH_eq_rootNum_mul` は `JH_eq_rootNum_mul_any` に含まれる。`removal_counterexample_four` の第 1 成分はほかの成分と無関係な証人。構築者の注記（B4 の後に足した）：全体として空虚ではない。法 2 に原始指標がないことは Lean の外）。'),
])
apply(N + 'pag2_part255_resolution_discrete_limit.md', [
 ('この行と次の「A2 が挙げたコメント」の行を足した（この直しは Part 258 の閉鎖条件 2 の照合 R2 を受けた）。',
  'この行と次の「A2 が挙げたコメント」の行を足した（この直しは Part 258 の閉鎖条件 2 の照合 R2 を受け、この行は R2 の指摘で書き直した。書き直しの照合は F3）。B4 の「38 行が §9 にない」は直していない（記録だけの指摘のため）。'),
])
apply(N + 'pag2_part254_full_gluing.md', [
 ('B4 の後に題の「法 M の」とこの行だけを足した（この直しは Part 258 の閉鎖条件 2 の照合 R2 を受けた）。',
  'B4 の後に題の「法 M の」とこの行だけを足した（この直しは Part 258 の閉鎖条件 2 の照合 R2 を受け、この行は R2 の指摘で書き直した。書き直しの照合は F3）。'),
 ('入力は PAG258.lean の最終版から機械的に起こし', '入力は PAG258.lean（Part 254）の最終版から機械的に起こし'),
])
apply(N + 'pag2_part257_local_factor_decomposition.md', [
 ('- 直したあと、PAG261 の形式文が同じこと、組み立て直した .out が同一であることを確かめた。この直しの後の照合：閉鎖条件の直しの照合（F3）で行う。',
  '- R4 の判定で残ったもの：§3-1 の重複定義の記録に、Part 189・190 の名前なしの同じ式（changeLevel の積）を足していない（内部照合の監査の記録 `pag2_internal_audit_249_256.md` に任せる）。§3-2 の `prod_map_div\'` は Mathlib の List 版が見つからないので残した。#9 の step280 のログは R4 に渡していなかった（ログは `audit257/step280.log`、11/11）。\n- 直したあと、PAG261 の形式文が同じこと、組み立て直した .out が同一であることを確かめた。この直しは閉鎖条件の直しの照合（F3）を受けた（形式文の変更なし、N1〜N7 は直った）。F3 の後に、`phaseA1_listChar` の docstring の繰り返しを直した（記録だけ、照合は受けていない）。'),
])
apply(L + 'PAG261.lean', [('（Lean で示したのは、成分がすべて原始のとき。原始でない指標では、phaseA1 は一般には W と違う）。 -/', '（原始でない指標では、phaseA1 は一般には W と違う。これは Lean の外）。 -/')])
for p, notesec in [(N + 'pag2_part252_hartley_gluing.md', 'B2 の段（B2 の判定と構築者の注記を分けた）'), (N + 'pag2_part256_gluing_cross_term.md', 'PAG260 の冒頭の説明の「範囲」の段の括弧（「（両辺 0 で）」を 1 つの文にまとめた）')]:
    s = open(p, encoding='utf-8').read()
    s += f'''
\n## 閉鎖条件 2 の照合（2026-11-14 夜、Part 258 の閉鎖条件）\n\n- 再照合の記録 §9 の B4 の後の直しを、照合者 R2 が照合した（`pag2_reaudit_252_256.md` §10、出力 `closing258/outputs/R2_output.md`）。このノートにかかわる直し：{notesec}。直しの照合は F3（`closing258/outputs/F3_output.md`）。F3 の後の直しは記録だけで、照合は受けていない。\n'''
    open(p, 'w', encoding='utf-8').write(s)
H = '/home/claude/out/final78/PAG2_handoff_part257.md'
s = open(H, encoding='utf-8').read(); s = s.replace('呼ばない）。 書くときは', '呼ばない）。書くときは'); open(H, 'w', encoding='utf-8').write(s)
print('ok')
