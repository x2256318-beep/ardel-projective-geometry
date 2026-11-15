#!/usr/bin/env python3
"""再照合の B2（照合）の依頼文を作る。

渡すもの（要約しない。原文のまま）：
 (1) 定義の全文（このファイルと前のファイル。コメントと docstring だけ除く）
 (2) 形式文の全文（このファイルの定理すべて。証明だけ除く）。★ は前回の照合の後に足した・変えた文
 (3) Lean ファイルの文面（冒頭の説明と docstring）
 (4) ノートの全文（行番号つき）と、前回の照合の時点の版から変わった行の範囲
 (5) 表（xlsx）の見出しと各行（主張・証明の要点）。★ は前回の照合の時点から足した・変えた行
 (6) A2 の出力の全文（あとで差し込む）と、名前の対応
"""
import difflib
import importlib.util
import json
import re
import sys

from openpyxl import load_workbook

sys.path.insert(0, '/home/claude/out/reaudit257')
from leanparse import parse, statement  # noqa: E402

PKG = '/home/claude/leanwork/pagpkg/'
OUT = '/home/claude/out/reaudit257/'
AUD = '/home/claude/out/'
NOTES = '/home/claude/out185/'
XLSX = '/home/claude/out/final75/lean_verification_status.xlsx'

HEAD = '''あなたは独立の照合者です。ある Lean 4（Mathlib）の形式化について、コンパイル済みの形式文と、それについて書かれた文面（ノート、表、Lean ファイルの docstring）を突き合わせ、文面が形式文の内容を正しく述べているかを判定してください。

## 守ってほしいこと
- ツールは一切使わないでください（ファイル、シェル、検索、エージェントの起動もしない）。
- 定義名・定理名は意味の根拠にしないでください。定義の本文と文の形で判断してください。
- 文面には、著者の解釈の言葉（貼り合わせ、素点、重なり、解像度、公準 A1 など）が出てきます。「読み」「解釈」と明示されていれば許容です。形式文の事実として書かれていれば、ずれとして挙げてください。
- 判断ごとに確信度（高・中・低）を付けてください。
- 回答は日本語で、6,000 字程度までにまとめてください。最後に、使ったツール（使っていなければ「なし」）を書いてください。
'''

TASK = '''
## 課題
1. 表（入力 (5)）：各行の主張と証明の要点を形式文と突き合わせ、「一致／主張が強い／主張が弱い／別物／偽」で判定してください。★ の行はすべて判定を書いてください。ほかの行は、ずれがあるものだけ挙げ、残りは「一致」とまとめて構いません。
2. ノート（入力 (4)）：題、冒頭の結論・位置づけ・読み、検証表、「Lean にしていないこと」を形式文と突き合わせてください。形式文より強い箇所、形式文にないことを形式文の事実として書いた箇所、解釈の言葉を事実として書いた箇所を、行番号つきで挙げてください。変わった行の範囲は必ず見てください。
3. Lean ファイルの文面（入力 (3)）：冒頭の説明と docstring について同じ観点で。★ の宣言は必ず見てください。
4. ★ の文について、A2 の訳と判定（入力 (6)）と、文面の言い方が食い違うところを挙げてください。
5. 直すべき点を重要な順に挙げてください。各点に、どこを、どう直すかを、形式文から起こした言い方の案で書いてください。
6. 全体：形式文に偽・空虚・別物があるか。標準を超える内容があるか。
'''


def defs_text(path, names=None, skip=()):
    _, ds = parse(path)
    out = []
    for d in ds:
        if d['kind'] in ('theorem', 'lemma'):
            continue
        if names is not None and d['name'] not in names:
            continue
        if d['name'] in skip:
            continue
        out.append(statement(d).strip())
    return out


def theorem_list(path):
    _, ds = parse(path)
    return [d for d in ds if d['kind'] in ('theorem', 'lemma')]


def docstrings(path):
    md, ds = parse(path)
    out = []
    if md:
        out.append('【ファイル冒頭の説明】\n' + md.strip())
    for d in ds:
        if d['doc']:
            nm = d['name'] or f"（名前のない {d['kind']}、{d['line']} 行目）"
            out.append(f"【{nm}】\n" + d['doc'].strip())
    return '\n\n'.join(out)


def numbered(path):
    lines = open(path, encoding='utf-8').read().split('\n')
    return '\n'.join(f'{i + 1:4d}| {l}' for i, l in enumerate(lines)), lines


def changed_ranges(base_path, final_lines):
    base = open(base_path, encoding='utf-8').read().split('\n')
    sm = difflib.SequenceMatcher(a=base, b=final_lines, autojunk=False)
    rs = []
    for tag, i1, i2, j1, j2 in sm.get_opcodes():
        if tag in ('replace', 'insert') and j2 > j1:
            rs.append((j1 + 1, j2))
    # 近いものをまとめる
    merged = []
    for a, b in rs:
        if merged and a <= merged[-1][1] + 2:
            merged[-1] = (merged[-1][0], max(b, merged[-1][1]))
        else:
            merged.append((a, b))
    return merged


def xlsx_rows(first, last):
    wb = load_workbook(XLSX, read_only=True)
    ws = wb['定理と証明']
    rows = list(ws.iter_rows(min_row=first, max_row=last, values_only=True))
    head = rows[0][0]
    assert all(r[0] == head for r in rows)
    return head, [(r[1], r[2], r[3]) for r in rows]


def load_rows_py(path):
    spec = importlib.util.spec_from_file_location('rows_mod', path)
    m = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(m)
    return getattr(m, 'HEAD', None), {r[0]: (r[1], r[2]) for r in m.ROWS}


def norm(x):
    return re.sub(r'\s+', '', str(x))


def build(key, lean, dep_defs, targets, note, note_base, xrange, xbase, a2_map, extra=''):
    ths = theorem_list(PKG + lean)
    # (2) 形式文の全文
    stm = []
    for d in ths:
        mark = '★ ' if d['name'] in targets else ''
        stm.append((f'-- {mark}' if mark else '') + ('\n' if mark else '') + statement(d).strip())
    # (1) 定義
    dd = []
    for path, names, skip in dep_defs:
        src = open(PKG + path, encoding='utf-8').read().split('\n')
        ctxl = [l for l in src if re.match(r'^(namespace |open (?!Classical in)|variable )', l)]
        dd += [f'-- {path}（文脈：' + ' / '.join(ctxl) + '）'] + defs_text(PKG + path, names, skip)
    # (4) ノート
    note_num, note_lines = numbered(NOTES + note)
    cr = changed_ranges(note_base, note_lines)
    crs = '、'.join(f'{a}〜{b}' if a != b else f'{a}' for a, b in cr)
    # (5) 表
    head, rows = xlsx_rows(*xrange)
    base_head, base_rows = xbase
    names_in_file = [d['name'] for d in ths]
    assert sorted(r[0] for r in rows) == sorted(names_in_file), key
    xl = [f'【見出し】{head}' + ('  ★（前回の照合の時点から変わった）' if base_head is not None and norm(base_head) != norm(head) else '')]
    star_rows = []
    for name, claim, proof in rows:
        b = base_rows.get(name)
        star = name in targets or b is None or norm(b[0]) != norm(claim) or norm(b[1]) != norm(proof)
        if star:
            star_rows.append(name)
        xl.append(f"{'★ ' if star else ''}{name}\n  主張：{claim}\n  証明の要点：{proof}")
    body = (HEAD + extra
            + '\n## 入力 (1)：定義の全文（このファイルと前のファイル。原文のまま。コメントと docstring だけ除いた）\n```lean\n'
            + '\n\n'.join(dd) + '\n```\n'
            + f'\n## 入力 (2)：形式文の全文（{lean} の定理 {len(ths)} 個すべて。原文のまま、証明だけ除いた。すべてコンパイル済みで sorry なし、公理は標準の範囲）\n'
            + '★ は、前回の照合の後に足した文・文を変えた文です。\n```lean\n' + '\n'.join(stm) + '\n```\n'
            + '\n## 入力 (3)：Lean ファイルの文面（ファイル冒頭の説明と、各宣言の docstring。原文のまま）\n```\n'
            + docstrings(PKG + lean) + '\n```\n'
            + f'\n## 入力 (4)：ノートの全文（原文のまま、行番号つき）\n前回の照合の時点の版から変わった行（または足した行）の範囲：{crs}\n```\n'
            + note_num + '\n```\n'
            + '\n## 入力 (5)：表（xlsx）の見出しと各行（原文のまま。主張と証明の要点。★ は前回の照合の時点の版から足した・変えた行）\n```\n'
            + '\n'.join(xl) + '\n```\n'
            + '\n## 入力 (6)：逆翻訳の査読者 A2 の出力の全文（原文のまま）\nA2 は ★ の文を、名前を中立化した入力で判定しました。名前の対応：'
            + a2_map + '\n\n{{A2_OUTPUT}}\n'
            + TASK)
    meta = dict(key=key, note_changed=cr, star_rows=star_rows, targets=sorted(targets), chars=len(body))
    return body, meta


def a2map(ren, names):
    inv = {v: k for k, v in ren.items()}
    keys = sorted({v for k, v in ren.items() if k in names}, key=lambda s: (s[0], int(re.sub(r'\D', '', s) or 0)))
    return '、'.join(f'{v} = `{inv[v]}`' for v in keys)


GLOSS_CHAR = '''
## Mathlib の前提
`ZMod N` は ℤ/N、`(ZMod N)ˣ` は単数群、`t.val` は 0 以上 N 未満の代表。`stdAddChar` は t ↦ exp(2πi·t.val/N)。`DirichletCharacter ℂ N` は法 N のディリクレ指標（単数でないところで 0）。`IsPrimitive` は導手が法に等しいこと、`Even` は χ(−1) = 1、`Odd` は χ(−1) = −1。`gaussSum χ ψ = Σ_a χ(a)ψ(a)`。`χ.conductor` は導手、`χ.primitiveCharacter` は χ を誘導する原始指標（法は導手）、`changeLevel h χ` は法を倍数に上げた指標。`ZMod.unitsMap h` は (ℤ/M)ˣ → (ℤ/N)ˣ の自然な準同型。`starRingEnd ℂ` は複素共役。`Submodule.span` は張る部分空間、`iSupIndep` は部分空間の族の独立、`⨆` は族の和。`Module.DirectLimit` は加群の帰納極限（代数的な直極限、完備化はしない）。`Complex.normSq z = |z|²`。
'''

GLOSS_255 = '''
## Mathlib の前提
`padicValRat p q` は有理数 q の p 進付値（ℤ 値。q = 0 では 0）。`Real.log` は自然対数（log 0 = 0、負の数では log |x|）。`Nat.Primes` は素数の部分型。`Nat.Primes → ℤ` には直積の位相が入る（ℤ は離散。近傍は有限個の座標を指定する集合を含む）。`BoxCoord` は同じ集合に別の位相を入れた型で、その位相は定義の `instance` のとおり。`Dense s` は閉包が全体、`closure` は閉包、`DiscreteTopology A` は部分空間の位相が離散、`T1Space` は 1 点集合が閉。`⊥`（位相）は離散位相。`f '' A` は像。
'''


def main():
    metas = []
    # Part 252
    ren = json.load(open(OUT + 'rename_252.json', encoding='utf-8'))
    _, b252 = None, {}
    # 前回の照合の時点の表：xlsx_part252_v1.xlsx（15 行）。S16〜S21 は照合 B に主張だけ渡した（中立化した文面）ので、表の行としては比べられない
    wb = load_workbook(AUD + 'audit252/xlsx_part252_v1.xlsx', read_only=True)
    ws = wb['定理と証明']
    old = list(ws.iter_rows(min_row=3373, max_row=3387, values_only=True))
    base_head = old[0][0]
    b252 = {r[1]: (r[2], r[3]) for r in old}
    body, meta = build('252', 'PAG256.lean', [('PAG256.lean', None, ())],
                       {'removal_counterexample_four'}, 'pag2_part252_hartley_gluing.md',
                       AUD + 'audit252/note_before_B.md', (3373, 3394), (base_head, b252),
                       a2map(ren, {'casKer', 'hartley', 'parFac', 'rootNum', 'JH', 'hartley_units_inv', 'neg_one_mul_self',
                                   'sum_mul_stdAddChar_neg', 'hartley_one', 'JH_eq_rootNum_mul_any',
                                   'removal_counterexample_normSq', 'removal_counterexample_four'}),
                       GLOSS_CHAR)
    open(OUT + 'prompt_B2_252.template.md', 'w', encoding='utf-8').write(body)
    metas.append(meta)
    # Part 254
    ren = json.load(open(OUT + 'rename_254.json', encoding='utf-8'))
    bh, br = load_rows_py(AUD + 'audit254/xlsx_rows_part254_v2_before_B.py')
    new = {'UA1_pullL_of_mem_Vprim', 'condPart_eq_map', 'ip_condPart', 'iSup_condPart', 'iSupIndep_condPart',
           'UA1_mem_condPart', 'ipLim_ofL_Vprim', 'condPart', 'ipR'}
    body, meta = build('254', 'PAG258.lean',
                       [('PAG256.lean', ['casKer', 'hartley', 'rootNum', 'JH'], ()),
                        ('PAG257.lean', None, ()), ('PAG258.lean', None, ())],
                       new, 'pag2_part254_full_gluing.md', AUD + 'audit254/note_v2_before_B_fixes.md',
                       (3429, 3485), (bh, br),
                       a2map(ren, set(ren) - {'ip_charU', 'span_charU_eq_top', 'eq_zero_of_ip_self'}) +
                       '。前のファイルの文：R1 = `ip_charU`、R2 = `span_charU_eq_top`、R3 = `eq_zero_of_ip_self`',
                       GLOSS_CHAR)
    open(OUT + 'prompt_B2_254.template.md', 'w', encoding='utf-8').write(body)
    metas.append(meta)
    # Part 255
    ren = json.load(open(OUT + 'rename_255.json', encoding='utf-8'))
    bh, br = load_rows_py(AUD + 'audit255/xlsx_rows_part255_v2.py')
    new = {'isClosed_and_discrete_of_subsingleton', 'dense_imgST_iff', 'isClosed_discrete_imgST',
           'isClosed_discrete_rhoBox_image', 'BoxCoord', 'rhoBox'}
    body, meta = build('255', 'PAG259.lean', [('PAG254.lean', ['logSet'], ()), ('PAG259.lean', None, ())],
                       new, 'pag2_part255_resolution_discrete_limit.md', AUD + 'audit255/note_v2_before_B.md',
                       (3486, 3530), (bh, br), a2map(ren, set(ren)), GLOSS_255)
    open(OUT + 'prompt_B2_255.template.md', 'w', encoding='utf-8').write(body)
    metas.append(meta)
    # Part 256
    ren = json.load(open(OUT + 'rename_256.json', encoding='utf-8'))
    bh, br = load_rows_py(AUD + 'audit256/xlsx_rows_part256_v1.py')
    body, meta = build('256', 'PAG260.lean',
                       [('PAG256.lean', ['parFac', 'rootNum'], ()), ('PAG257.lean', ['charU', 'ip'], ()),
                        ('PAG258.lean', ['conductor_neZero', 'phaseA1', 'UA1'], ()), ('PAG260.lean', None, ())],
                       {'rootNum_prodChar_ne_mul', 'rootNum_prodChar_eq_neg_mul'}, 'pag2_part256_gluing_cross_term.md',
                       AUD + 'audit256/note_v1_before_audit.md', (3531, 3553), (bh, br),
                       a2map(ren, set(ren) - {'rootNum_eq', 'rootNum_ne_zero', 'phaseA1_of_isPrimitive', 'UA1_charU',
                                              'exists_primitive_odd_three', 'isPrimitive_of_prime_of_ne_one'}) +
                       '。前のファイルの文：R1 = `rootNum_eq`、R2 = `rootNum_ne_zero`、R3 = `phaseA1_of_isPrimitive`、R4 = `UA1_charU`、R5 = `exists_primitive_odd_three`、R6 = `isPrimitive_of_prime_of_ne_one`',
                       GLOSS_CHAR)
    open(OUT + 'prompt_B2_256.template.md', 'w', encoding='utf-8').write(body)
    metas.append(meta)
    json.dump(metas, open(OUT + 'prompt_B2_meta.json', 'w', encoding='utf-8'), ensure_ascii=False, indent=1)
    for m in metas:
        print(m['key'], m['chars'], 'note changed', len(m['note_changed']), 'star rows', len(m['star_rows']))


if __name__ == '__main__':
    main()
