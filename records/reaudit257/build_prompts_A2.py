#!/usr/bin/env python3
"""再照合の A2（逆翻訳、中立化）の依頼文を作る。

入力は Lean ファイルの最終版から機械的に起こす（要約しない）。名前だけを中立化する。
定義は内容をそのまま渡し、線形写像の証明の義務（map_add'・map_smul'）と、定義の中の証明の項だけを省く（省いたことを明記する）。
"""
import json
import re
import sys

sys.path.insert(0, '/home/claude/out/reaudit257')
from leanparse import parse, statement  # noqa: E402

PKG = '/home/claude/leanwork/pagpkg/'
OUT = '/home/claude/out/reaudit257/'
AUD = '/home/claude/out/'

HEAD = '''あなたは独立の査読者です。ある Lean 4（Mathlib）の形式化の定義と形式文を読み、意味を正確に訳して判定してください。構築の経緯や意図は知らせません。名前は中立化してあります（Φ・Ψ・Θ・Ξ・Ω は定義、S・R は定理）。

## 守ってほしいこと
- ツールは一切使わないでください（ファイル、シェル、検索、エージェントの起動もしない）。
- 判断ごとに確信度（高・中・低）を付けてください。
- 回答は日本語で、5,000 字程度までにまとめてください。最後に、使ったツール（使っていなければ「なし」）を書いてください。
'''

TASK = '''
## 課題
1. 入力 (3) の各文（{targets}）を、量化子・暗黙の引数・仮定を落とさずに数学の言葉に訳してください。
2. 各文を判定してください：実質的（標準）／実質的（標準を超える可能性）／自明／ほぼ同語反復／条件つきで弱い／端の場合だけ（具体例・証人）／偽または空虚の疑い。理由を短く。
3. 仮定の点検：各仮定を外すと偽になるか、不要な仮定はないか、仮定が空虚に満たされないか（満たす例があるか）。
4. 定義の点検：入力 (3) の文に出てくる定義が、何を表しているか。気になる点（規約、型の選び方、位相などの構造の入れ方、法や引数の順など）があれば挙げてください。
5. 全体の所見：入力 (3) の文で言えていること・言えていないこと。入力 (2) の文との関係（言い換え・特別な場合・独立）にも触れてください。
'''


def neutralize(text, ren):
    t = re.sub(r'PAG\.Part\d+\.', '', text)
    for k in sorted(ren, key=len, reverse=True):
        t = re.sub(r'(?<![\w.])' + re.escape(k) + r'(?![\w])', ren[k], t)
    return t


def theorems(path):
    _, ds = parse(path)
    return [d for d in ds if d['kind'] in ('theorem', 'lemma')]


def block(stmts):
    return '```lean\n' + '\n'.join(stmts) + '\n```\n'


def check_no_leak(text, words):
    bad = [w for w in words if re.search(r'(?<![\w])' + re.escape(w) + r'(?![\w])', text)]
    assert not bad, bad


# ---------- Part 252（PAG256） ----------
def part252():
    ren = json.load(open(AUD + 'audit252/rename.json', encoding='utf-8'))
    ren['removal_counterexample_four'] = 'S22'
    ths = theorems(PKG + 'PAG256.lean')
    names = [d['name'] for d in ths]
    assert names[-1] == 'removal_counterexample_four' and len(names) == 22
    ctx, tgt = [], []
    for d in ths:
        s = neutralize(statement(d), ren)
        n = int(ren[d['name']][1:])
        (ctx if n <= 15 else tgt).append(s)
    defs = open(AUD + 'audit252/defs_neutral.lean', encoding='utf-8').read().strip()
    gloss = '''
## Mathlib の前提
`ZMod N` は ℤ/N、`(ZMod N)ˣ` は単数群、`t.val` は 0 以上 N 未満の代表。`stdAddChar` は t ↦ exp(2πi·t.val/N)。`DirichletCharacter ℂ N` は法 N のディリクレ指標（ZMod N → ℂ、単数でないところで 0）。`IsPrimitive` は導手が N に等しいこと、`Even` は χ(−1) = 1、`Odd` は χ(−1) = −1。`gaussSum χ ψ = Σ_a χ(a)ψ(a)`。`Complex.normSq z = |z|²`。`IsUnit x` は x が単数。`(1 : DirichletCharacter ℂ N)` は自明な指標（単数で 1、単数でないところで 0）。
'''
    body = (HEAD + gloss
            + '\n## 入力 (1)：定義（このファイルの定義。内容は原文のまま、名前だけ置き換えた）\n' + block([defs])
            + '\n## 入力 (2)：同じファイルの文（S1〜S15。文脈として示す。判定の対象ではない。すべてコンパイル済みで sorry なし、公理は標準の 3 つ以内）\n' + block(ctx)
            + '\n## 入力 (3)：判定の対象の文（S16〜S22。すべてコンパイル済みで sorry なし、公理は標準の 3 つ以内）\n' + block(tgt)
            + TASK.format(targets='S16〜S22'))
    check_no_leak(body, ['hartley', 'rootNum', 'casKer', 'parFac', 'JH', 'removal_counterexample_four'])
    return body, ren


# ---------- Part 254（PAG258） ----------
def part254():
    ren = json.load(open(AUD + 'audit254/rename_v2.json', encoding='utf-8'))
    new = ['UA1_pullL_of_mem_Vprim', 'condPart_eq_map', 'ip_condPart', 'iSup_condPart',
           'iSupIndep_condPart', 'UA1_mem_condPart', 'ipLim_ofL_Vprim']
    for i, n in enumerate(new):
        ren[n] = f'S{51 + i}'
    ren['condPart'] = 'Ω1'
    ren['ipR'] = 'Ω2'
    # 前のファイルの文（文脈）
    ren['ip_charU'] = 'R1'
    ren['span_charU_eq_top'] = 'R2'
    ren['eq_zero_of_ip_self'] = 'R3'
    ths = theorems(PKG + 'PAG258.lean')
    assert [d['name'] for d in ths][-7:] == new and len(ths) == 57
    ctx, tgt = [], []
    for d in ths:
        s = neutralize(statement(d), ren)
        (tgt if d['name'] in new else ctx).append(s)
    deps = []
    for d in theorems(PKG + 'PAG257.lean'):
        if d['name'] in ('ip_charU', 'span_charU_eq_top', 'eq_zero_of_ip_self'):
            deps.append(neutralize(statement(d), ren))
    assert len(deps) == 3
    defs = open(AUD + 'audit254/defs_neutral_v2.lean', encoding='utf-8').read().strip()
    defs = defs.replace('-- 以下は S18〜S50 で使う定義（独立照合 A・C の後に足したもの）', '-- 以下は S18〜S57 で使う定義')
    defs += '''

-- 以下は S51〜S57 で使う定義
noncomputable def Ω1 (N : ℕ) [NeZero N] (q : ℕ) : Submodule ℂ ((ZMod N)ˣ → ℂ) :=
  Submodule.span ℂ (Set.range fun χ : {χ : DirichletCharacter ℂ N // χ.conductor = q} => Ψ4 χ.1)

noncomputable def Ω2 (f : (ZMod N)ˣ → ℂ) : ((ZMod N)ˣ → ℂ) →ₗ[ℂ] ℂ where
  toFun := Ψ5 f
  -- map_add'・map_smul' の証明は省略'''
    gloss = open(AUD + 'audit254/prompt_A.md', encoding='utf-8').read()
    gloss = gloss[gloss.index('## Mathlib の前提'):gloss.index('## 入力 (1)')]
    gloss = '\n' + gloss.strip() + ' `iSupIndep F` は部分空間の族 F が独立（各 F q と、ほかの F j の和との共通部分が 0）。`⨆ q, F q` は族の和（張る部分空間）。`Module.DirectLimit` は加群の帰納極限（代数的な直極限、完備化はしない）。\n'
    body = (HEAD + gloss
            + '\n## 入力 (1)：定義（内容は原文のまま、名前だけ置き換えた。線形写像の証明の義務と、定義の中の証明の項は省いた。ファイルではすべてコンパイル済み）\n' + block([defs])
            + '\n## 入力 (2)：文脈として示す文（判定の対象ではない。すべてコンパイル済みで sorry なし）\n'
            + '前のファイルの文：\n' + block(deps)
            + '同じファイルの文（S1〜S50）：\n' + block(ctx)
            + '\n## 入力 (3)：判定の対象の文（S51〜S57。すべてコンパイル済みで sorry なし、公理は標準の 3 つ以内）\n' + block(tgt)
            + TASK.format(targets='S51〜S57。あわせて定義 Ω1・Ω2'))
    check_no_leak(body, ['UA1', 'condPart', 'ipR', 'Vprim', 'charU', 'ipLim', 'ofL', 'pullL', 'TopL', 'phaseA1', 'rootNum'])
    return body, ren


# ---------- Part 255（PAG259） ----------
def part255():
    ren = json.load(open(AUD + 'audit255/rename_v2.json', encoding='utf-8'))
    ths = theorems(PKG + 'PAG259.lean')
    new = ['isClosed_and_discrete_of_subsingleton', 'dense_imgST_iff', 'isClosed_discrete_imgST',
           'isClosed_discrete_rhoBox_image']
    order = [d['name'] for d in ths if d['name'] in new]
    assert order == new, order
    for i, n in enumerate(new):
        ren[n] = f'S{42 + i}'
    ren['BoxCoord'] = 'Ξ3'
    ren['logSet'] = 'Ξ1'
    ren['rhoBox'] = 'Φ2'
    assert len(ths) == 45 and all(d['name'] in ren for d in ths)
    ctx, tgt = [], []
    for d in ths:
        s = neutralize(statement(d), ren)
        (tgt if d['name'] in new else ctx).append(s)
    defs = '''noncomputable def Φ1 (q : ℚ) : ℝ × (Nat.Primes → ℤ) := (Real.log q, fun p => padicValRat p q)

def Ξ2 (S T : Finset ℕ) : Set (ℝ × (T → ℤ)) :=
  {z | ∃ q : ℚ, 0 < q ∧ (∀ t : ℕ, t.Prime → t ∉ S → padicValRat t q = 0) ∧
    z = (Real.log q, fun t : T => padicValRat (t : ℕ) q)}

-- S42〜S45 で使う定義（型 Ξ3 は Nat.Primes → ℤ と同じ集合で、位相だけを入れ替えたもの）
def Ξ3 : Type := Nat.Primes → ℤ

instance : TopologicalSpace Ξ3 := ⊥

instance : DiscreteTopology Ξ3 := ⟨rfl⟩

noncomputable def Φ2 (q : ℚ) : ℝ × Ξ3 := (Real.log q, fun p => padicValRat p q)

-- 前のファイルの定義
def Ξ1 : Set ℝ := {x | ∃ q : ℚ, 0 < q ∧ x = Real.log q}'''
    gloss = open(AUD + 'audit255/prompt_A.md', encoding='utf-8').read()
    gloss = gloss[gloss.index('## Mathlib の前提'):gloss.index('## 入力 (1)')]
    gloss = '\n' + gloss.strip() + ' `⊥`（位相）は離散位相。`T1Space` は 1 点集合が閉じている空間。`DiscreteTopology A`（A は部分集合）は部分空間の位相が離散であること。`(U ∩ A).Subsingleton` は U ∩ A の点が高々 1 つ。`nhds z` は z の近傍フィルター。\n'
    body = (HEAD + gloss
            + '\n## 入力 (1)：定義（内容は原文のまま、名前だけ置き換えた）\n' + block([defs])
            + '\n## 入力 (2)：同じファイルの文（S1〜S41。文脈として示す。判定の対象ではない。すべてコンパイル済みで sorry なし）\n' + block(ctx)
            + '\n## 入力 (3)：判定の対象の文（S42〜S45。すべてコンパイル済みで sorry なし、公理は標準の 3 つ以内）\n' + block(tgt)
            + TASK.format(targets='S42〜S45。あわせて定義 Ξ3（とその位相）・Φ2'))
    check_no_leak(body, ['rho', 'imgST', 'BoxCoord', 'rhoBox', 'logSet', 'threshold_iff'])
    return body, ren


# ---------- Part 256（PAG260） ----------
def part256():
    ren = json.load(open(AUD + 'audit256/rename.json', encoding='utf-8'))
    ren['rootNum_prodChar_eq_neg_mul'] = 'S23'
    ren['ip'] = 'Ξ6'
    for k, v in {'rootNum_eq': 'R1', 'rootNum_ne_zero': 'R2', 'phaseA1_of_isPrimitive': 'R3',
                 'UA1_charU': 'R4', 'exists_primitive_odd_three': 'R5',
                 'isPrimitive_of_prime_of_ne_one': 'R6'}.items():
        ren[k] = v
    ths = theorems(PKG + 'PAG260.lean')
    assert len(ths) == 23 and all(d['name'] in ren for d in ths)
    ctx, tgt = [], []
    for d in ths:
        s = neutralize(statement(d), ren)
        (tgt if d['name'] in ('rootNum_prodChar_ne_mul', 'rootNum_prodChar_eq_neg_mul') else ctx).append(s)
    deps = []
    for f, ns in [('PAG256.lean', ['rootNum_eq', 'exists_primitive_odd_three', 'isPrimitive_of_prime_of_ne_one']),
                  ('PAG257.lean', ['rootNum_ne_zero']), ('PAG258.lean', ['phaseA1_of_isPrimitive', 'UA1_charU'])]:
        for d in theorems(PKG + f):
            if d['name'] in ns:
                deps.append(neutralize(statement(d), ren).replace('(χ : DirichletCharacter ℂ N)', '(χ : DirichletCharacter ℂ n)')
                            .replace('DirichletCharacter ℂ N}', 'DirichletCharacter ℂ n}').replace('(Real.sqrt N : ℂ)', '(Real.sqrt n : ℂ)'))
    assert len(deps) == 6
    defs = '''variable {M N : ℕ} [NeZero M] [NeZero N]

-- このファイルの定義
noncomputable def Φ1 (χ₁ : DirichletCharacter ℂ M) (χ₂ : DirichletCharacter ℂ N) :
    DirichletCharacter ℂ (M * N) :=
  changeLevel (dvd_mul_right M N) χ₁ * changeLevel (dvd_mul_left N M) χ₂

def Ψ1 (M N : ℕ) [NeZero M] [NeZero N] (x : ZMod M × ZMod N) : ZMod (M * N) :=
  ((x.1.val * N + x.2.val * M : ℕ) : ZMod (M * N))

open Classical in
noncomputable def Θ1 (χ₁ : DirichletCharacter ℂ M) (χ₂ : DirichletCharacter ℂ N) : ℂ :=
  if χ₁.Odd ∧ χ₂.Odd then -1 else 1

-- 前のファイルの定義（n は法、[NeZero n]）
open Classical in
noncomputable def Ξ1 (χ : DirichletCharacter ℂ n) : ℂ :=
  gaussSum χ stdAddChar / ((if χ.Even then (1 : ℂ) else I) * (Real.sqrt n : ℂ))

noncomputable def Ξ2 (χ : DirichletCharacter ℂ n) : ℂ := ((1 - I) + (1 + I) * χ (-1)) / 2

instance (χ : DirichletCharacter ℂ n) : NeZero χ.conductor := ⟨conductor_ne_zero (χ := χ)⟩

noncomputable def Ξ3 (χ : DirichletCharacter ℂ n) : ℂ := Ξ1 χ.primitiveCharacter

def Ξ5 (χ : DirichletCharacter ℂ n) : (ZMod n)ˣ → ℂ := fun u => χ u

noncomputable def Ξ6 (f g : (ZMod n)ˣ → ℂ) : ℂ := ∑ u, (starRingEnd ℂ) (f u) * g u

noncomputable def Ξ4 : ((ZMod n)ˣ → ℂ) →ₗ[ℂ] ((ZMod n)ˣ → ℂ) where
  toFun f := ∑ χ : DirichletCharacter ℂ n,
    (Ξ3 χ * Ξ6 (Ξ5 χ) f / (Nat.totient n : ℂ)) • Ξ5 χ
  -- map_add'・map_smul' の証明は省略'''
    gloss = open(AUD + 'audit256/prompt_A.md', encoding='utf-8').read()
    gloss = gloss[gloss.index('## Mathlib の前提'):gloss.index('## 入力 (1)')]
    gloss = '\n' + gloss.strip() + '\n'
    body = (HEAD + gloss
            + '\n## 入力 (1)：定義（内容は原文のまま、名前だけ置き換えた。線形写像の証明の義務は省いた）\n' + block([defs])
            + '\n## 入力 (2)：文脈として示す文（判定の対象ではない。すべてコンパイル済みで sorry なし）\n'
            + '前のファイルの文（n は法）：\n' + block(deps)
            + '同じファイルの文（S1〜S17、S19〜S22）：\n' + block(ctx)
            + '\n## 入力 (3)：判定の対象の文（S18・S23。すべてコンパイル済みで sorry なし、公理は標準の 3 つ以内）\n' + block(tgt)
            + TASK.format(targets='S18・S23'))
    check_no_leak(body, ['rootNum', 'prodChar', 'crossSign', 'phaseA1', 'UA1', 'charU', 'crtMap', 'parFac'])
    return body, ren


if __name__ == '__main__':
    for key, fn in [('252', part252), ('254', part254), ('255', part255), ('256', part256)]:
        body, ren = fn()
        open(OUT + f'prompt_A2_{key}.md', 'w', encoding='utf-8').write(body)
        json.dump(ren, open(OUT + f'rename_{key}.json', 'w', encoding='utf-8'), ensure_ascii=False, indent=1)
        print(key, len(body))
