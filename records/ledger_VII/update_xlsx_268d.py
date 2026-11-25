"""統合照合 VII の指摘（VI の低 1 の残り）：Part 264 の xlsx の LABEL に「線形の」を、索引 2.4・PAG268 の冒頭・ノートと揃えて入れる。"""
import openpyxl, shutil, os
R = '/home/claude/ardel-projective-geometry/verification/lean_verification_status.xlsx'
wb = openpyxl.load_workbook(R); ws = wb['定理と証明']; n = 0
old, new = 'トーラス等変な延長の一意性', 'トーラス等変な線形の延長の族の一意性'
for r in range(3758, 3772):
    v = ws.cell(r, 1).value
    if v and old in v:
        ws.cell(r, 1).value = v.replace(old, new); n += 1
wb.save(R)
if os.path.isdir('/home/claude/out/final86'):
    shutil.copy(R, '/home/claude/out/final86/lean_verification_status.xlsx')
print('label cells', n)
