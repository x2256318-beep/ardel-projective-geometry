"""Part 263 の閉鎖（2026-11-25 19:11 の著者の判断）による xlsx の LABEL の直し。
コミット 5419967 で、手で書いた同じ内容のスクリプトを 1 回実行した（34 セル）。統合照合 III-b・IV の指摘で、その内容をこのファイルに書き起こした（2026-11-25 夜。再実行しても置き換える文字列がないので何もしない）。"""
import openpyxl
R = '/home/claude/ardel-projective-geometry/verification/lean_verification_status.xlsx'
wb = openpyxl.load_workbook(R); ws = wb['定理と証明']; n = 0
for r in range(3724, 3758):
    v = ws.cell(r, 1).value
    if v and 'ラベル（見込み、閉鎖で確定）' in v:  # 統合照合 V-a の指摘で空のセルに備えた
        ws.cell(r, 1).value = v.replace('ラベル（見込み、閉鎖で確定）', 'ラベル（2026-11-25 19:11 の閉鎖で確定）'); n += 1
wb.save(R); print('label cells', n)
