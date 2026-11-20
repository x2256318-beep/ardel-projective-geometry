"""台帳 L10（照合 R3 の後の直し）の照合の入力。2026-11-20。"""
import subprocess, pathlib, openpyxl
R = pathlib.Path('/home/claude/ardel-projective-geometry'); L = pathlib.Path('/home/claude/leanwork/pagpkg')
def rd(p): return pathlib.Path(p).read_text(encoding='utf-8')
def git(*a): return subprocess.run(['git', *a], cwd=R, capture_output=True, text=True).stdout
def code(s, lang=''): return f'```{lang}\n{s.rstrip()}\n```\n'
o = ['# 照合の入力：照合 R3 の後の直し（台帳 L10）（2026-11-20 夕方）\n',
     '照合の対象：§B の差分。§A は前の照合（照合 R3）の出力の全文で、§B の直しが答えるべき指摘。§C〜§E は根拠。\n',
     '\n## §A 照合 R3 の出力（全文）\n', rd(R/'records/audit266/recheck_L9/outputs/R3_output.md'),
     '\n## §B 差分（コミット 768cb6b → a92e59b。R3 の出力・メタ・照合者のスクリプト・xlsx・名前の照合の記録は除く）\n',
     code(git('diff', '768cb6b', 'a92e59b', '--', '.', ':!records/audit266/recheck_L9', ':!verification', ':!records/founding_index/check_names.log'), 'diff'),
     '\n## §C PAG266.lean の全文（現在）とビルドの記録\n', code(rd(L/'PAG266.lean'), 'lean'),
     '2026-11-20 15:5x に PAG265・PAG266 を作り直した：終了コード 0、エラー・警告・sorry の行は 0、#print axioms は 15 行すべて [propext, Classical.choice, Quot.sound]。\n']
wb = openpyxl.load_workbook(R/'verification/lean_verification_status.xlsx'); ws = wb['定理と証明']
rows = [f'行 {r} の列 A：' + str(ws.cell(r, 1).value) for r in (3719,)]
memo = next(ws.cell(r, 1).value for r in range(3724, ws.max_row+1) if isinstance(ws.cell(r,1).value, str) and ws.cell(r,1).value.startswith('メモ'))
rows.append('メモの末尾（500 字）：…' + memo[-500:])
o += ['\n## §D xlsx（final84）の Part 262 の行の列 A（5 行とも同じ文）とメモの末尾（現在）\n', code('\n\n'.join(rows))]
o += ['\n## §E 尾の台帳（現在、全文）\n', code(rd(R/'notes/pag2_tail_ledger.md'), 'markdown')]
t = '\n'.join(o)
(R/'records/audit266/recheck_L10/input_R4.md').write_text(t, encoding='utf-8'); pathlib.Path('/home/claude/out/int266/input_R4.md').write_text(t, encoding='utf-8')
print(len(t.split('\n')), 'lines', 'Author:' in t)
