"""統合照合 II-a（台帳 L3・L4）と II-b（台帳 L1・L2・L5）の入力を組み立てる。2026-11-20。"""
import subprocess, pathlib, re
R = pathlib.Path('/home/claude/ardel-projective-geometry'); L = pathlib.Path('/home/claude/leanwork/pagpkg')
def rd(p): return pathlib.Path(p).read_text(encoding='utf-8')
def git(*a): return subprocess.run(['git', *a], cwd=R, capture_output=True, text=True).stdout
def code(s, lang=''): return f'```{lang}\n{s.rstrip()}\n```\n'
def lines_from(p, start_pat, end_pat=None):
    ls = rd(p).split('\n'); a = next(i for i, l in enumerate(ls) if re.search(start_pat, l))
    b = len(ls) if end_pat is None else next((i for i in range(a+1, len(ls)) if re.search(end_pat, ls[i])), len(ls))
    return '\n'.join(ls[a:b])
led = rd(R/'notes/pag2_tail_ledger.md')
def ledger_item(k):
    i = led.index(f'### {k}'); j = led.find('### L', i+5); j2 = led.index('## 閉じた項目')
    return led[i:(j if 0 < j < j2 else j2)]
# ---------- II-a ----------
o = ['# 統合照合 II-a の入力：尾の台帳 L3（Part 260（PAG264）の統合照合の後の直し）と L4（Part 261（PAG265）の再照合の後の直し）（2026-11-20）\n',
     '照合の対象：§L3-4 と §L4-4 の「直した後の散文」のうち、前の照合の出力（§L3-1・§L4-1）を受けて直した文。直す前の散文（§L3-2・§L4-2）と比べて、直しが指摘を正しく反映したか、形式文（§L3-3・§L4-3 の Lean の全文）より強いことを言っていないか、新しいずれを生んでいないかを見る。\n']
o += ['\n## §L3 台帳 L3\n', code(ledger_item('L3'), 'markdown')]
o += ['\n### §L3-1 Part 260 の統合照合の出力（`records/audit264/outputs/integrated_output.md`、全文）\n', rd(R/'records/audit264/outputs/integrated_output.md')]
s = rd(R/'records/audit264/input_integrated.md'); i = s.index('## C. 散文その 1')
o += ['\n### §L3-2 直す前の散文（統合照合に渡した版：PAG264 の冒頭の説明、ノートの §1〜§3・§8）\n', s[i:]]
o += ['\n### §L3-2b 統合照合に渡した定義と前の鎖の補題の文\n', s[s.index('## B. 使う定義'):i]]
o += ['\n### §L3-3 現在の PAG264.lean の全文（docstring を含む）\n', code(rd(L/'PAG264.lean'), 'lean')]
o += ['\n### §L3-4 現在のノート `notes/pag2_pag264_corner_maps.md`（全文）\n', code(rd(R/'notes/pag2_pag264_corner_maps.md'), 'markdown')]
o += ['\n## §L4 台帳 L4\n', code(ledger_item('L4'), 'markdown')]
o += ['\n### §L4-1 Part 261 の再照合（3 回目の照合）の出力（`records/audit265/outputs/recheck_output.md`、全文）と、その入力にあった前の指摘\n', rd(R/'records/audit265/outputs/recheck_output.md'), '\n#### 前の指摘（`records/audit265/input_prev_findings.md`）\n', rd(R/'records/audit265/input_prev_findings.md')]
o += ['\n### §L4-2 直す前の散文と形式文（再照合に渡した版）\n', '\n#### `records/audit265/input_prose.md`\n', rd(R/'records/audit265/input_prose.md'), '\n#### `records/audit265/input_formal.md`\n', rd(R/'records/audit265/input_formal.md')]
o += ['\n### §L4-3 現在の PAG265.lean の全文（docstring を含む）\n', code(rd(L/'PAG265.lean'), 'lean')]
o += ['\n### §L4-4 現在のノート `notes/pag2_pag265_corner_limit.md`（全文）\n', code(rd(R/'notes/pag2_pag265_corner_limit.md'), 'markdown')]
o += ['\n### §L4-5 L4 の範囲のコミット 6ba1a54 の、PAG265.lean とノートの差分（コミットの中に、再照合の前の直しと後の直しが混ざっている）\n', code(git('show', '--format=', '6ba1a54', '--', 'PAG265.lean', 'notes/pag2_pag265_corner_limit.md'), 'diff')]
ta = '\n'.join(o)
# ---------- II-b ----------
o = ['# 統合照合 II-b の入力：尾の台帳 L1・L2・L5（基礎文書の材料索引と記録の直し）（2026-11-20）\n',
     '照合の対象：§L1・§L2・§L5 の差分で追加・変更された文。前の照合の出力（T3、T4r2）を受けた直しは、指摘を正しく反映したか、形式文・数値の記録・ほかのファイルと食い違わないか、地位・決定者・日付が強められていないかを見る。著者の発言の原文はこの入力にない（記録に引用された部分だけ）。決定の中身を原文と照らすことはできないので、記録どうしの整合を見る。\n']
o += ['\n## §L1 台帳 L1\n', code(ledger_item('L1'), 'markdown')]
o += ['\n### §L1-1 2 回目の再照合の出力（`records/tail_audit4/outputs/T4r2_output.md`、全文）\n', rd(R/'records/tail_audit4/outputs/T4r2_output.md')]
o += ['\n### §L1-2 差分（コミット e52f57b → 41c4526。記録の入力・出力のファイルは除く）\n', code(git('diff', 'e52f57b', '41c4526', '--', '.', ':!records/tail_audit4', ':!records/audit264_identity', ':!records/limit_form/audit_crt'), 'diff')]
o += ['\n### §L1-3 同じ範囲で足した照合の出力（根拠）\n', '\n#### `records/limit_form/audit_crt/outputs/crt_output.md`\n', rd(R/'records/limit_form/audit_crt/outputs/crt_output.md'), '\n#### `records/audit264_identity/outputs/identity_output.md`\n', rd(R/'records/audit264_identity/outputs/identity_output.md')]
def decl(f, n):
    s = rd(L/f); m = re.search(rf'(/--(?:(?!-/).)*?-/\s*\n)?(?:open [^\n]*in\n)?(?:noncomputable )?(?:theorem|lemma|def) {re.escape(n)}\b.*?(?=\n\n|\n/--|\ntheorem |\nlemma |\ndef |\nnoncomputable def )', s, re.S)
    return m.group(0) if m else f'-- 見つからない {n}'
o += ['\n### §L1-4 差分で docstring を直した宣言と、索引 5.5 の次元の式で引く宣言（現在の版）\n']
for f, n in [('PAG264.lean','cornerHom'),('PAG264.lean','existsUnique_corner'),('PAG265.lean','cornerSys')]:
    o += [f'\n#### {f} の {n}\n', code(decl(f, n), 'lean')]
for f in sorted(L.glob('PAG2*.lean')):
    if re.search(r'theorem finrank_shellAlg_primePow\b', rd(f)):
        o += [f'\n#### {f.name} の finrank_shellAlg_primePow\n', code(decl(f.name, 'finrank_shellAlg_primePow'), 'lean')]; break
o += ['\n## §L2 台帳 L2\n', code(ledger_item('L2'), 'markdown'), '\n### §L2-1 差分（コミット 41c4526 → 27ccadf）\n', code(git('diff', '41c4526', '27ccadf'), 'diff')]
o += ['\n## §L5 台帳 L5\n', code(ledger_item('L5'), 'markdown')]
o += ['\n### §L5-1 索引の第 2 版の照合（統合照合 T3）の出力（`records/tail_audit3/outputs/T3_output.md`、全文）\n', rd(R/'records/tail_audit3/outputs/T3_output.md')]
o += ['\n### §L5-2 差分（コミット 153e91d → deab9f3。T3 の後の直し＝索引の第 3 版と、同じコミットの材料ノート・文献照合ノート・CLAUDE.md の直し、第 4 版・第 5 版の著者の決定の記録）\n',
      '注：台帳 L5 は索引だけを挙げていたが、同じコミット 47e5860 の材料ノート第 7 版・文献照合ノート第 5 版・CLAUDE.md の直しも T3 の後の直しで、照合を受けた記録がない。この照合の入力に含めた（入力を組み立てるときに見つけた）。\n',
      code(git('diff', '153e91d', 'deab9f3', '--', 'notes/', 'CLAUDE.md', 'CLAUDE.en.md'), 'diff')]
o += ['\n### §L5-3 補足 15 の受け取りと照らし合わせ（コミット 27ccadf → 11a8e26 の差分。補足 15 の本文を含む）\n', code(git('diff', '27ccadf', '11a8e26'), 'diff')]
tb = '\n'.join(o)
out = pathlib.Path('/home/claude/out/int266'); out.mkdir(parents=True, exist_ok=True)
for name, t in [('input_IIa.md', ta), ('input_IIb.md', tb)]:
    (R/'records/audit266/integrated'/name).write_text(t, encoding='utf-8'); (out/name).write_text(t, encoding='utf-8')
    print(name, len(t.split('\n')), 'lines', '見つからない' in t)
