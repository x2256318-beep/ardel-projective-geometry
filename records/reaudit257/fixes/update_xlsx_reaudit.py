#!/usr/bin/env python3
"""再照合（補足3）による xlsx の直し（final75 → final76）。見出しと行の主張・証明の要点の文面だけを直し、行は足さない。
検証手順に 1 行（手順 277）を足し、メモを更新する。"""
import copy
from openpyxl import load_workbook
SRC = '/home/claude/out/final75/lean_verification_status.xlsx'
DST = '/home/claude/out/final76/lean_verification_status.xlsx'
wb = load_workbook(SRC)
ws = wb['定理と証明']

def rows_of(name_first, name_last, first, last):
    assert ws.cell(first, 2).value == name_first and ws.cell(last, 2).value == name_last, (ws.cell(first, 2).value, ws.cell(last, 2).value)
    return range(first, last + 1)

def set_head(rng, old_sub, new_head=None, replace=None):
    h = ws.cell(rng[0], 1).value
    assert all(ws.cell(r, 1).value == h for r in rng)
    if replace:
        a, b = replace
        assert h.count(a) == 1, a
        nh = h.replace(a, b)
    else:
        assert old_sub in h
        nh = new_head
    for r in rng:
        ws.cell(r, 1).value = nh

def fix(name, col, a, b, rng):
    rs = [r for r in rng if ws.cell(r, 2).value == name]
    assert len(rs) == 1, name
    v = ws.cell(rs[0], col).value
    assert v.count(a) == 1, (name, a[:40])
    ws.cell(rs[0], col).value = v.replace(a, b)

R252 = rows_of('casKer_eq', 'removal_counterexample_four', 3373, 3394) if ws.cell(3373, 2).value == 'casKer_eq' else None
# Part 252 の行の範囲（xlsx では最後の行が removal_counterexample_four とは限らないので、見出しで範囲を取る）
h252 = ws.cell(3373, 1).value
R252 = range(3373, 3395)
assert all(ws.cell(r, 1).value == h252 for r in R252) and ws.cell(3395, 1).value != h252
set_head(R252, 'PAG2.0-252', new_head='PAG2.0-252 離散 Hartley 変換 H_N（正規化しない）と反転 J の合成 J∘H_N/√N は、単数の上で各原始指標 χ を W(χ) 倍する（単数の上の式はすべての指標で成り立つ。W は原始指標ならルート数）。読み：構築者が再構成したモノグラフ §1.3 の主張 (2)、U = J∘H_N/√N の原始指標の部分（公理 A1 の境界ユニタリの原始指標の部分）。U と A1 は Lean の文に出てこない（著者の判断 3「Lean 化してください」。重なりの読みはねじれた貼り合わせ U）')
fix('removal_counterexample_normSq', 3, '除去テストの反例（|W| = 1）：法 2 の自明な指標（原始的でない）で |rootNum|² = 1/2（原始指標のない法での例）',
    '法 2 の自明な指標で |rootNum|² = 1/2。原始的でないことは removal_counterexample の第 1 成分で、2 つを合わせて |W| = 1 の除去テストの反例になる（法 2 に原始指標がないことは Lean の外）', R252)

R254 = range(3429, 3486)
assert ws.cell(3429, 2).value == 'rootNum_congr' and ws.cell(3485, 2).value == 'ipLim_ofL_Vprim'
set_head(R254, None, replace=('重なりはねじれた貼り合わせ U と決定済み', '重なりの読みはねじれた貼り合わせ U'))
fix('TopL_not_compat', 3, '自明な指標で T(π f) ≠ π(T f)', 'ある f : (ℤ/1)ˣ → ℂ で T(π f) ≠ π(T f)（証明の証人は自明な指標）', R254)
fix('UA1_star', 3, '（U_N(conj ∘ f) = conj ∘ U_N f。U_N の核は実数値で、定理 2.6 の条件 KUK = U。',
    '（U_N(conj ∘ f) = conj ∘ U_N f。「U_N の核は実数値」「KUK = U」は同値な言い換えで、Lean の文ではない。', R254)
fix('eq_zero_of_ipLim_self', 3, '極限の内積の非退化：⟨z, z⟩ = 0 なら z = 0', '極限の内積の定値性：⟨z, z⟩ = 0 なら z = 0（正値は ipLim_self_nonneg）', R254)
fix('iSupIndep_condPart', 3, '導手ごとの部分は独立（iSupIndep）。iSup_condPart・condPart_eq_map と合わせて、単数の上の関数の空間は ⊕_{q∣M} π_{q→M}(V_prim(q)) の直交直和（Part 252 の残る問い 1 の直和の文。独立照合 B の指摘で追加）',
    '導手ごとの部分は独立（iSupIndep。添字は q ∈ ℕ 全体）。ip_condPart（直交）・iSup_condPart（張る）・condPart_eq_map（各部分の形）と合わせると ⊕_{q∣M} π_{q→M}(V_prim(q)) の直交直和になるが、1 つの定理にはしていない（q ∤ M の部分が 0 であることも文にしていない。Part 252 の残る問い 1 の直和の部品。独立照合 B の指摘で追加）', R254)

R255 = range(3486, 3531)
assert ws.cell(3486, 2).value == 'padicValRat_prime_ne' and ws.cell(3530, 2).value == 'exists_between_one'
fix('closure_logSet', 3, '∞ だけを測って完備化すると ℝ 全体：log ℚ_{>0} の閉包は ℝ（Part 250 の dense_logSet から。著者の定義では解像度が落ちた姿）',
    '∞ だけを測る：log ℚ_{>0} の閉包は ℝ（Part 250 の dense_logSet から。閉包を完備化と読み、著者の定義の「解像度が落ちる」にあたると読むのは読み）', R255)
fix('threshold_iff', 3, '（著者の定義では、閉包に連続体が入る＝解像度が落ちる）', '（閉包に連続体が入ることを、著者の定義の「解像度が落ちる」にあたると読むのは読み）', R255)
fix('fiber_sep', 3, '（c = log p、または S ⊆ T なら c = 1 で必ず等しい。独立照合 A の指摘で追加）',
    '（文が言うのは c > 0 の存在だけ。証明では S ∖ T = {p} なら c = log p、S ⊆ T なら 2 元は等しい。独立照合 A の指摘で追加）', R255)

R256 = range(3531, 3554)
assert ws.cell(3531, 2).value == 'cast_crtMap_fst' and ws.cell(3553, 2).value == 'charU_prodChar'
set_head(R256, 'PAG2.0-256', new_head='PAG2.0-256 互いに素な法の原始指標の積の上での UA1 の固有値の式（読み：貼り合わせ U の固有値）：交差項の法則 W(χ₁χ₂) = s·χ₁(N)·χ₂(M)·W(χ₁)·W(χ₂)（著者が 2026-11-13 18:15 に候補 M1 を選んだ。既知の事実の Lean 化：Montgomery–Vaughan の Theorem 9.6 とそのルート数版。文献では、大域の ε 因子が局所の積であることと、不分岐なひねりでの局所 ε 因子の変化から出る形にあたる。局所 ε 因子は Lean にしていない）')
fix('rootNum_prodChar_ne_mul', 3, '（存在の例 1 つ。比の値 ∓i は文にない）', '（存在の文。条件を満たす 2 組のどちらでも成り立つ。比の値 ∓i は文にない）', R256)
fix('rootNum_prodChar_ne_mul', 4, 's = −1、χ₁(5) = −1、χ₂(3)² = −1 なので比 χ₂(3) ≠ 1',
    's = −1、χ₁(5) = −1 なので W(χ₁χ₂) = χ₂(3)·W(χ₁)W(χ₂)。χ₂(3)² = −1 で χ₂(3) ≠ 1、W(χ₁)W(χ₂) ≠ 0', R256)
fix('rootNum_prodChar_eq_neg_mul', 3, '（独立照合 B の手計算の例を Lean にした）',
    '（独立照合 B の手計算の例を Lean にした）。交差項が 1 なので τ(χ₁χ₂) = τ(χ₁)·τ(χ₂) で、−1 は W の正規化（奇×奇で i·i = −1）から来る', R256)

# メモ
done = False
for r in range(3554, ws.max_row + 1):
    v = ws.cell(r, 1).value
    if isinstance(v, str) and v.startswith('メモ：'):
        a = 'PAG260 は 2026-11-13 に同じ環境でコンパイル（追加のビルドなし）。'
        assert a in v
        ws.cell(r, 1).value = v.replace(a, a + '2026-11-14、著者側の補足3 による再照合のあと、PAG256・PAG258・PAG259・PAG260 の文面（冒頭の説明と docstring）だけを直し、PAG256〜PAG260 を同じ環境で組み立て直した（形式文は変えていない）。Part 252・254・255・256 の見出しと行の文面の一部も直した（行は足していない）。')
        done = True
assert done

ws2 = wb['検証手順']
assert str(ws2.cell(277, 1).value) == '276'
ws2.insert_rows(278, amount=1)
vals = [277, '再照合（著者側の補足3、2026-11-14）：Part 252・254・255・256 の照合を受けていない残件（照合の後に足した Lean の文と、照合の後に直した文面）を、新しいエージェント A2（逆翻訳）4 体・B2（照合）4 体で照合し、文面（Lean の冒頭の説明と docstring、ノート、表）を形式文に合わせて直した。PAG256〜PAG260 を組み立て直した', '完了',
        '形式文に偽・空虚・別物なし、標準を超える内容なし（4 Part とも）。ずれは文面の側（B の後の直しが Lean の docstring に入っていなかった、など）。照合者には形式文と定義の全文、ノートの全文、表の全行、A2 の出力の全文を渡した（入力ファイルを Read で読む形。ツール使用は Read だけ、1〜4 回）。記録は pag2_reaudit_252_256.md']
for c, v in enumerate(vals, start=1):
    cell = ws2.cell(278, c); cell.value = v
    src = ws2.cell(277, c)
    cell.font = copy.copy(src.font); cell.alignment = copy.copy(src.alignment); cell.border = copy.copy(src.border); cell.fill = copy.copy(src.fill)
fixed2 = 0
for r in range(279, ws2.max_row + 1):
    v = ws2.cell(r, 2).value
    if isinstance(v, str) and v.startswith('=COUNTIF($C$2:$C$277'):
        ws2.cell(r, 2).value = v.replace('$C$277', '$C$278').replace('$A$277', '$A$278')
        fixed2 += 1
assert fixed2 == 1, fixed2
wb.save(DST)
print('saved', DST)
