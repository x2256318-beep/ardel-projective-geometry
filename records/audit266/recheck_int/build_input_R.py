"""統合照合の後の直し（台帳 L7）と台帳の外の直し（L8）の再照合の入力。2026-11-20。"""
import subprocess, pathlib, re, openpyxl
R = pathlib.Path('/home/claude/ardel-projective-geometry'); L = pathlib.Path('/home/claude/leanwork/pagpkg')
def rd(p): return pathlib.Path(p).read_text(encoding='utf-8')
def git(*a): return subprocess.run(['git', *a], cwd=R, capture_output=True, text=True).stdout
def code(s, lang=''): return f'```{lang}\n{s.rstrip()}\n```\n'
def decl(f, n):
    s = rd(L/f); m = re.search(rf'(/--(?:(?!-/).)*?-/\s*\n)?(?:open [^\n]*in\n)?(?:noncomputable )?(?:theorem|lemma|def|abbrev) {re.escape(n)}\b.*?(?=\n\n|\n/--|\ntheorem |\nlemma |\ndef |\nnoncomputable def |\nopen )', s, re.S)
    return m.group(0) if m else f'-- 見つからない {n}'
o = ['# 再照合の入力：統合照合（2026-11-20 朝）の後の直し（台帳 L7）と、台帳の外に見つかった直し（L8）\n',
     '照合の対象：§B の差分（L7）と §C の差分（L8）。§A は前の照合（統合照合 I・II-a・II-b）の出力の全文で、§B の直しが答えるべき指摘。§D〜§G は根拠。\n']
o += ['\n## §A 統合照合の出力（全文）\n']
for k in ['I', 'IIa', 'IIb']:
    o += [f'\n### §A-{k}（`records/audit266/integrated/outputs/{k}_output.md`）\n', rd(R/f'records/audit266/integrated/outputs/{k}_output.md')]
o += ['\n## §B 統合照合の後の直しの差分（コミット 7354404 → 9c73149。記録の出力・xlsx・名前の照合の記録は除く）\n',
      code(git('diff', '7354404', '9c73149', '--', '.', ':!records/audit266/integrated', ':!verification', ':!records/founding_index/check_names.log'), 'diff')]
o += ['\n## §C 台帳 L8 の差分（コミット 153e91d → deab9f3 の概要と引き継ぎメモ）\n', code(git('diff', '153e91d', 'deab9f3', '--', 'docs/', 'handoff/'), 'diff')]
o += ['\n## §D Lean の根拠\n', '\n### §D-1 PAG266.lean の全文（現在）\n', code(rd(L/'PAG266.lean'), 'lean')]
for f, n in [('PAG24.lean','equator_intertwine'),('PAG25.lean','equator_intertwine_hat'),('PAG246.lean','finrank_shellAlg_primePow'),('PAG242.lean','finrank_shellAlg_primePow'),
             ('PAG265.lean','exists_local_unit'),('PAG265.lean','ofCorner_one_mul_self'),('PAG265.lean','exists_local_unit_finset'),('PAG265.lean','not_exists_left_one'),
             ('PAG264.lean','existsUnique_corner'),('PAG264.lean','cornerOp_comp'),('PAG264.lean','cornerOp_mul'),('PAG264.lean','cornerOp_pull')]:
    o += [f'\n### {f} の {n}（文だけでなく証明も含む抜き出し）\n', code(decl(f, n), 'lean')]
o += ['\n### §D-2 PAG264・PAG265 の冒頭の説明（現在）\n']
for f in ['PAG264.lean', 'PAG265.lean']:
    s = rd(L/f); o += [f'\n#### {f}\n', code(s[:s.index('-/')+2], 'lean')]
o += ['\n### §D-3 ビルドと確かめの記録\n',
      '2026-11-20 08:00 ごろ、PAG264・PAG265・PAG266 を作り直した。終了コード 0、エラー・警告・sorry の行は 0、#print axioms は 55 行すべて [propext, Classical.choice, Quot.sound]。\n',
      '\n#### `#synth` と `#check`（`records/audit266/recheck_int/Synth265.lean` とその出力）\n', code(rd(R/'records/audit266/recheck_int/Synth265.lean'), 'lean'), code(rd(R/'records/audit266/recheck_int/Synth265.out')),
      '\n#### 1 行の確かめ（`Idem.lean`。出力は空＝エラーなし）\n', code(rd(R/'records/audit266/recheck_int/Idem.lean'), 'lean'), code(rd(R/'records/audit266/recheck_int/Idem.out') or '（空）')]
o += ['\n## §E 数値の記録（直したスクリプトとログ）\n', code(rd(R/'records/audit266/numeric/unit_point_ratio.py'), 'python'), code(rd(R/'records/audit266/numeric/unit_point_ratio.log')),
      '\n### 依存するスクリプト `records/p1_gluing/equator_U_check.py`（docstring に注を足した。計算は変えていない）\n', code(rd(R/'records/p1_gluing/equator_U_check.py'), 'python')]
wb = openpyxl.load_workbook(R/'verification/lean_verification_status.xlsx'); ws = wb['定理と証明']
rows = [f'行 {r}：' + ' ｜ '.join(str(ws.cell(r, c).value) for c in range(1, 7)) for r in range(3719, 3724)]
memo = next(ws.cell(r, 1).value for r in range(3724, ws.max_row+1) if isinstance(ws.cell(r,1).value, str) and ws.cell(r,1).value.startswith('メモ'))
rows.append('メモの末尾（700 字）：…' + memo[-700:]); ws2 = wb['検証手順']; rows.append('検証手順 行 285：' + ' ｜ '.join(str(ws2.cell(285, c).value) for c in range(1, 5)))
o += ['\n## §F xlsx（final84）の Part 262 の行とメモ・検証手順（現在。直しは `records/audit266/update_xlsx_266b.py`）\n', code('\n\n'.join(rows)), code(rd(R/'records/audit266/update_xlsx_266b.py'), 'python')]
o += ['\n## §G 尾の台帳（現在、全文）\n', code(rd(R/'notes/pag2_tail_ledger.md'), 'markdown')]
o += ['\n## §H 構築側が WebFetch の要約で確かめた文献の記述（2026-11-20）\n',
      '- arXiv:1410.6179（Long–Pigno–Pinner）：式 (10) は J(χ_1, …, χ_k, p^m) = ∏ G(χ_i, p^m) / G(χ_1⋯χ_k, p^m)。χ_1, …, χ_k と積がすべて原始的なとき。k = 2 は Zhang–Yao の補題 3、一般の k は Zhang–Xu の補題 1。正規化したガウス和 τ/(i^a √q) による式は書かれていない（WebFetch の要約）。\n',
      '- K. Conrad, Gauss and Jacobi sums on finite fields and ℤ/mℤ：定理 3.12「χ が法 m の原始指標なら |G(χ)| = √m」、定理 3.15「法 m の χ_1, χ_2 の積が原始的なら G(χ_1)G(χ_2) = J(χ_1, χ_2)G(χ_1χ_2)」。m は一般（WebFetch の要約）。\n',
      '- `records/gamma_corner/outputs/blind_output.md` の Q5 の結びの文（原文）：「使ったのは超距離（木）の組合せ構造とポントリャーギン双対性だけで、ℤ に固有の算術は使っていない。」（確信度：中〜高）\n']
t = '\n'.join(o)
out = pathlib.Path('/home/claude/out/int266'); out.mkdir(parents=True, exist_ok=True)
(R/'records/audit266/recheck_int/input_R.md').write_text(t, encoding='utf-8'); (out/'input_R.md').write_text(t, encoding='utf-8')
print(len(t.split('\n')), 'lines', '見つからない' in t, 'x2256318' in t, 'Author:' in t)
