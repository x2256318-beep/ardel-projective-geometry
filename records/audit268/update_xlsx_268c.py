"""Part 264 の閉鎖（2026-11-25 22:28 の著者の判断）による xlsx の LABEL の直し。"""
import openpyxl, shutil
R = '/home/claude/ardel-projective-geometry/verification/lean_verification_status.xlsx'
wb = openpyxl.load_workbook(R); ws = wb['定理と証明']; n = 0
for r in range(3758, 3772):
    v = ws.cell(r, 1).value
    if 'ラベル（見込み、閉鎖で確定）' in v:
        ws.cell(r, 1).value = v.replace('ラベル（見込み、閉鎖で確定）', 'ラベル（2026-11-25 22:28 の閉鎖で確定）'); n += 1
wb.save(R); shutil.copy(R, '/home/claude/out/final86/lean_verification_status.xlsx'); print('label cells', n)
