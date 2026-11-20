"""再照合 R2（2026-11-20 15:15〜15:31）の指摘を受けた xlsx（final84）の直し。行は増やさない。
ラベルの「統合照合の後に確定」を「見込み。Part を閉じるときに確定」に戻す（統合照合はラベルを確定していない）。"""
import openpyxl, shutil
p = '/home/claude/ardel-projective-geometry/verification/lean_verification_status.xlsx'
wb = openpyxl.load_workbook(p); ws = wb['定理と証明']
for r in range(3719, 3724):
    c = ws.cell(r, 1); v = c.value
    a = 'ラベル（統合照合の後に確定）は 1 が［既知］、2〜5 が［再導出（小さい）］'
    assert v.count(a) == 1, r
    c.value = v.replace(a, 'ラベル（見込み。Part を閉じるときに確定）は 1 が［既知］、2〜5 が［再導出（小さい）］')
memo_r = next(r for r in range(3724, ws.max_row + 1) if isinstance(ws.cell(r, 1).value, str) and ws.cell(r, 1).value.startswith('メモ'))
c = ws.cell(memo_r, 1); a = '統合照合の後の直しは台帳の L7。'
assert c.value.count(a) == 1
c.value = c.value.replace(a, '統合照合の後の直しは台帳の L7、その再照合（R2）の後の直しは L9。')
wb.save(p); shutil.copy(p, '/home/claude/out/final84/lean_verification_status.xlsx'); print('ok')
