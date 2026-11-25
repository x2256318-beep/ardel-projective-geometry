"""統合照合 I-a の指摘による xlsx の直し（2026-11-25）。"""
import openpyxl, shutil
R = '/home/claude/ardel-projective-geometry/verification/lean_verification_status.xlsx'
wb = openpyxl.load_workbook(R); ws = wb['定理と証明']
reps = {
 '（N = 1 では等しい）': '（N = 1 では等しい：Lean の外、手計算）',
 '（合成数の法では赤道の外は 0・∞ だけではない）': '（合成数の法では赤道の外は 0・∞ だけではない：Lean の外）',
 'Part 24 の mk_inv_eq': 'Part 24（PAG28）の mk_inv_eq',
 'Part 24 の Wpull': 'Part 24（PAG28）の Wpull',
 'Lim（Part 254）': 'Lim（Part 254（PAG258））',
 'Part 254 の Lim': 'Part 254（PAG258）の Lim',
 '0 延長は極限に降りない。': '0 延長は極限に降りない（各段の 0 延長と一致する線形写像がない。resL の切断の存在は否定しない）。',
}
n = 0
for r in range(3724, 3758):
    for c in range(1, 6):
        v = ws.cell(r, c).value
        if isinstance(v, str):
            w = v
            for a, b in reps.items():
                if a in w and b not in w: w = w.replace(a, b)
            if w != v: ws.cell(r, c).value = w; n += 1
wb.save(R); shutil.copy(R, '/home/claude/out/final85/lean_verification_status.xlsx'); print('cells changed', n)
