"""統合照合 III-a の指摘による xlsx の直し（2026-11-25）。"""
import openpyxl, shutil
R = '/home/claude/ardel-projective-geometry/verification/lean_verification_status.xlsx'
wb = openpyxl.load_workbook(R); ws = wb['定理と証明']
reps = {
 '法 N の式をそのまま使うと原始的でない χ では両立しない。': '法 N の式をそのまま使うと原始的でない χ では両立しない場合がある（証人 1 つ）。',
 '（法 N の式は原始的でない χ で両立しない）': '（法 N の式は原始的でない χ で両立しない場合がある。法 3 → 9 のように両立する例もある：Lean の外）',
}
n = 0
for r in range(3758, 3772):
    for c in range(1, 6):
        v = ws.cell(r, c).value
        if isinstance(v, str):
            w = v
            for a, b in reps.items():
                if a in w and b not in w: w = w.replace(a, b)
            if w != v: ws.cell(r, c).value = w; n += 1
    if ws.cell(r, 2).value == 'torus_eqPt': ws.cell(r, 5).value = '（rfl、定義どおり）'; n += 1
wb.save(R); shutil.copy(R, '/home/claude/out/final86/lean_verification_status.xlsx'); print('cells changed', n)
