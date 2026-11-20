"""照合 R3（2026-11-20 15:37〜15:45）の指摘を受けた xlsx（final84）の直し：留保の引用に「照合した範囲では」を足す。行は増やさない。"""
import openpyxl, shutil
p = '/home/claude/ardel-projective-geometry/verification/lean_verification_status.xlsx'
wb = openpyxl.load_workbook(p); ws = wb['定理と証明']
a = '基礎文書の索引 2.4 の留保「`JH` と P¹ のモデルを結ぶ Lean の文はない」に関わる材料'
b = '基礎文書の索引 2.4 の留保「照合した範囲（PAG23・PAG26・PAG27・PAG256）では `JH` と P¹ のモデルを結ぶ Lean の文はない」に関わる材料'
for r in range(3719, 3724):
    c = ws.cell(r, 1); assert c.value.count(a) == 1, r; c.value = c.value.replace(a, b)
memo_r = next(r for r in range(3724, ws.max_row + 1) if isinstance(ws.cell(r, 1).value, str) and ws.cell(r, 1).value.startswith('メモ'))
c = ws.cell(memo_r, 1); a = 'その再照合（R2）の後の直しは L9。'; assert c.value.count(a) == 1
c.value = c.value.replace(a, 'その再照合（R2）の後の直しは L9、L9 の照合（R3）の後の直しは L10。')
wb.save(p); shutil.copy(p, '/home/claude/out/final84/lean_verification_status.xlsx'); print('ok')
