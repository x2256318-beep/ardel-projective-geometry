"""統合照合（2026-11-20 07:43〜07:55）の指摘を受けた xlsx（final84）の直し。行は増やさない。"""
import openpyxl, shutil
p = '/home/claude/ardel-projective-geometry/verification/lean_verification_status.xlsx'
wb = openpyxl.load_workbook(p); ws = wb['定理と証明']
def fix(cell, a, b):
    v = cell.value; assert isinstance(v, str) and v.count(a) == 1, (cell.coordinate, a[:40]); cell.value = v.replace(a, b)
for r in range(3719, 3724):
    c = ws.cell(r, 1)
    fix(c, '基礎文書の索引 1.4・2.4 の留保「P¹ のモデルと結ぶ Lean の文はない」を埋める材料）',
        '基礎文書の索引 2.4 の留保「`JH` と P¹ のモデルを結ぶ Lean の文はない」に関わる材料。`JH` と P¹ のモデルを結ぶ文ではなく、留保は残る）')
    fix(c, 'ラベルは 1〜3 が［既知］、4・5 が［再導出（小さい）］',
        'ラベル（統合照合の後に確定）は 1 が［既知］、2〜5 が［再導出（小さい）］（符号つきの形を書いた文献は見つかっていない）')
    fix(c, '`JH` と P¹ のモデルを結ぶ文ではない。ラベル', 'ラベル')
memo_r = next(r for r in range(3724, ws.max_row + 1) if isinstance(ws.cell(r, 1).value, str) and ws.cell(r, 1).value.startswith('メモ'))
c = ws.cell(memo_r, 1)
fix(c, 'Part 262（PAG266.lean、短期層、舞台 P¹ の赤道の絡み合いを 𝔀 で書く）', 'Part 262（PAG266.lean、短期層、舞台 P¹ の赤道の絡み合いの係数を 𝔀（rootNum）で書く）')
fix(c, '再照合の後の直し（文面のみ、形式文は変えていない）は尾の台帳の L6 で、閉じるときの統合照合の対象。',
    '再照合の後の直し（形式文は変えていない。Lean の外の新しい文（単数の点の比）と数値を含む）は尾の台帳の L6 で、統合照合（2026-11-20、照合者 3 人）の対象にした。統合照合の後の直しは台帳の L7。')
ws2 = wb['検証手順']
c = ws2.cell(285, 4)
fix(c, '内部照合（言葉の検索で Part 21 の equator_intertwine_hat と Part 25 の equator_intertwine_proj を使った。',
    '内部照合（言葉の検索で Part 21（PAG25）の equator_intertwine_hat と Part 25（PAG29）の equator_intertwine_proj を使った。')
fix(c, '独立照合・再照合（記録は records/audit266/outputs/）。再照合の後の直しは尾の台帳の L6。',
    '独立照合・再照合（記録は records/audit266/outputs/）、統合照合（records/audit266/integrated/）。再照合の後の直しは尾の台帳の L6、統合照合の後の直しは L7。')
c = ws2.cell(285, 2)  # 注（2026-11-20、再照合 R2 の指摘）：この行とその次の fix は置き換え前と後が同じで、何も変えていない
fix(c, '（舞台 P¹ の赤道の絡み合いの係数を 𝔀（rootNum）で書く：', '（舞台 P¹ の赤道の絡み合いの係数を 𝔀（rootNum）で書く：')
wb.save(p); shutil.copy(p, '/home/claude/out/final84/lean_verification_status.xlsx'); print('ok', memo_r)
