"""統合照合 I（Part 262 の材料と台帳 L6）の入力を組み立てる。2026-11-20。"""
import re, subprocess, pathlib, openpyxl
R = pathlib.Path('/home/claude/ardel-projective-geometry'); L = pathlib.Path('/home/claude/leanwork/pagpkg')
out = []
def sec(t): out.append(f'\n## {t}\n')
def code(s, lang=''): out.append(f'```{lang}\n{s.rstrip()}\n```\n')
def rd(p): return pathlib.Path(p).read_text(encoding='utf-8')
def lean_decl(file, name, kw=r'(?:theorem|lemma|def|abbrev|noncomputable def|structure|instance)'):
    s = rd(L / file); lines = s.split('\n')
    pat = re.compile(rf'^\s*(?:@\[[^\]]*\]\s*)?(?:private\s+)?{kw}\s+{re.escape(name)}(?=[\s:({{\[]|$)')
    for i, ln in enumerate(lines):
        if pat.search(ln):
            j = i
            while j > 0 and (lines[j-1].strip().startswith('/--') or lines[j-1].strip().startswith('--') or (lines[j-1].strip() and not lines[j-1].strip().startswith(('theorem','lemma','def','noncomputable','variable','end','section','namespace','open','include','omit','instance','abbrev','@['))) and '-/' in ''.join(lines[max(0,j-8):j])):
                j -= 1
                if lines[j].strip().startswith('/--'): break
            k = i + 1
            while k < len(lines) and lines[k].strip() and not re.match(r'^(theorem|lemma|def|noncomputable|/--|end |section|@\[|instance|abbrev|open |variable|include|omit)', lines[k]):
                k += 1
            return '\n'.join(lines[j:k])
    return f'-- 見つからない: {name} in {file}'
out.append('# 統合照合 I の入力：Part 262（PAG266、短期層）の材料と、尾の台帳 L6（2026-11-20）\n')
out.append('照合の対象：§D の散文（Lean の冒頭の説明と docstring、ノート、索引・辞書・xlsx・引き継ぎメモ・台帳の Part 262 の行）と、§F の着手前の文書。§E の差分は再照合の後の直し（台帳 L6）で、照合を受けていない。§A〜§C と §G は根拠。\n')
sec('§A PAG266.lean の全文（現在の版。docstring と冒頭の説明を含む）')
code(rd(L / 'PAG266.lean'), 'lean')
sec('§B ビルドの記録')
out.append('`lake env lean PAG266.lean` 相当のビルド（2026-11-20 07:36、再照合の後の直しの後）。終了コード 0、出力は次の 5 行だけ（エラー・警告・sorry の行は 0）。\n')
code(rd('/tmp/b266.log'))
sec('§C 使う定義と補題の文')
s = rd(R / 'records/audit266/input_recheck.md'); i = s.index('## §D 使う定義と補題の文')
out.append(s[i:].split('\n', 1)[1])
out.append('\n### 追加（再照合の照合者が入力になかったと申告した定義）\n')
for f, n in [('PAG23.lean','P1F'),('PAG23.lean','Compat'),('PAG26.lean','Pt'),('PAG26.lean','toP1'),('PAG26.lean','ofP1'),('PAG26.lean','ptEquiv'),('PAG27.lean','toProj'),('PAG27.lean','projEquiv'),('PAG28.lean','projFun_eq'),('PAG28.lean','projFun_south')]:
    out.append(f'\n#### PAG.Part{f[3:-5]}.{n}（{f}）\n'); code(lean_decl(f, n), 'lean')
sec('§D 散文（照合の対象）')
out.append('\n### D1 ノート `notes/pag2_pag266_p1_equator_rootnum.md`（全文）\n'); code(rd(R/'notes/pag2_pag266_p1_equator_rootnum.md'), 'markdown')
idx = rd(R/'notes/pag2_founding_material_index.md').split('\n')
def block(lines, start_pat, end_pat):
    a = next(i for i, l in enumerate(lines) if re.search(start_pat, l)); b = next(i for i in range(a+1, len(lines)) if re.search(end_pat, lines[i]))
    return '\n'.join(lines[a:b])
out.append('\n### D2 材料索引 `notes/pag2_founding_material_index.md` の 1.4 と 2.4（節の全文）\n')
code(block(idx, r'^\*\*1\.4 ', r'^## 第 2 章'), 'markdown'); code(block(idx, r'^\*\*2\.4 ', r'^\*\*2\.5 '), 'markdown')
dic = rd(R/'notes/pag2_terwilliger_dictionary.md').split('\n')
out.append('\n### D3 辞書 `notes/pag2_terwilliger_dictionary.md` の §19・§20\n'); code(block(dic, r'^## 19\.', r'^## 21\.|^ZZZ') if any(l.startswith('## 21.') for l in dic) else '\n'.join(dic[next(i for i,l in enumerate(dic) if l.startswith('## 19.')):]), 'markdown')
wb = openpyxl.load_workbook(R/'verification/lean_verification_status.xlsx'); ws = wb['定理と証明']
out.append('\n### D4 xlsx（final84）の行 3719〜3723（列 A〜F）と、メモの末尾、検証手順の行 285\n')
rows = []
for r in range(3719, 3724):
    rows.append(f'行 {r}：' + ' ｜ '.join(str(ws.cell(r, c).value) for c in range(1, 7)))
memo = next(ws.cell(r, 1).value for r in range(3724, ws.max_row+1) if isinstance(ws.cell(r,1).value, str) and ws.cell(r,1).value.startswith('メモ'))
rows.append('メモの末尾（600 字）：…' + memo[-600:])
ws2 = wb['検証手順']; rows.append('検証手順 行 285：' + ' ｜ '.join(str(ws2.cell(285, c).value) for c in range(1, 5)))
code('\n\n'.join(rows))
ho = rd(R/'handoff/PAG2_handoff_part259.md'); out.append('\n### D5 引き継ぎメモ `handoff/PAG2_handoff_part259.md` の Part 262 の項\n'); code(ho[ho.index('- **Part 262（PAG266'):], 'markdown')
led = rd(R/'notes/pag2_tail_ledger.md'); out.append('\n### D6 尾の台帳 `notes/pag2_tail_ledger.md` の L6\n'); code(led[led.index('### L6'):led.index('## 閉じた項目')], 'markdown')
sec('§E 再照合の出力（全文）と、その後の直しの差分（台帳 L6）')
out.append('\n### E1 再照合の出力 `records/audit266/outputs/recheck_output.md`\n'); out.append(rd(R/'records/audit266/outputs/recheck_output.md'))
out.append('\n### E2 再照合の後の直しの差分（コミット e669d83 → 5f675ec。xlsx・記録の出力・名前の照合の記録は除く）\n')
d = subprocess.run(['git','diff','e669d83','5f675ec','--','PAG266.lean','notes/','handoff/','records/audit266/update_xlsx_266.py','records/audit266/numeric/'], cwd=R, capture_output=True, text=True).stdout
code(d, 'diff')
sec('§F 着手前の文書 `notes/pag2_p1_gluing_preregistration.md`（全文、照合の対象）')
code(rd(R/'notes/pag2_p1_gluing_preregistration.md'), 'markdown')
sec('§G 数値の記録と盲検の出力（根拠）')
for f in ['records/audit266/numeric/unit_point_ratio.py','records/audit266/numeric/unit_point_ratio.log','records/p1_gluing/equator_U_check.py','records/p1_gluing/equator_U_check.log','records/p1_gluing/equator_solution_count.py','records/p1_gluing/equator_solution_count.log','records/p1_gluing/control_fqt_equator.py','records/p1_gluing/control_fqt_equator.log','records/p1_gluing/blind_claims_check.py','records/p1_gluing/blind_claims_check.log','records/p1_gluing/outputs/blind_meta.txt','records/p1_gluing/outputs/blind_output.md']:
    out.append(f'\n### {f}\n'); code(rd(R/f), 'python' if f.endswith('.py') else '')
pathlib.Path('/home/claude/out/int266').mkdir(parents=True, exist_ok=True)
txt = '\n'.join(out); (R/'records/audit266/integrated/input_I.md').write_text(txt, encoding='utf-8')
pathlib.Path('/home/claude/out/int266/input_I.md').write_text(txt, encoding='utf-8')
print(len(txt.split('\n')), 'lines')
