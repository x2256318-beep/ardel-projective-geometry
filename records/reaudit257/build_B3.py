#!/usr/bin/env python3
"""B3（直しの照合）の入力を作る。形式文と定義の全文（B2 と同じ）、B2 の出力の全文、直しの前後の差分（Lean・ノート・表）を渡す。"""
import difflib
from openpyxl import load_workbook
R = '/home/claude/out/reaudit257/'
D = open(R + 'inbox_dir.txt').read().strip()
BF = R + 'before_fixes/'
PARTS = {
 '252': ('PAG256', 'pag2_part252_hartley_gluing.md', (3373, 3394)),
 '254': ('PAG258', 'pag2_part254_full_gluing.md', (3429, 3485)),
 '255': ('PAG259', 'pag2_part255_resolution_discrete_limit.md', (3486, 3530)),
 '256': ('PAG260', 'pag2_part256_gluing_cross_term.md', (3531, 3553)),
}
HEAD = '''あなたは独立の照合者です。ある Lean 4（Mathlib）の形式化について、前の照合者（B2）が文面のずれを指摘し、構築者が文面を直しました。直しが正しく入ったかを、形式文と突き合わせて判定してください。

## 守ってほしいこと
- この入力ファイルを Read で読んだあとは、ツールを一切使わないでください（ほかのファイル、シェル、検索、Web、エージェントの起動もしない）。長くて 1 回で読み切れないときは、同じファイルの続き（offset を指定）を読むことだけ許します。
- 定義名・定理名は意味の根拠にしないでください。定義の本文と文の形で判断してください。
- 著者の解釈の言葉（貼り合わせ、素点、重なり、解像度、公準 A1 など）は、「読み」「解釈」と明示されていれば許容です。
- 判断ごとに確信度（高・中・低）を付けてください。回答は日本語で、3,000 字程度までにまとめてください。最後に Read の回数を書いてください。
'''
TASK = '''
## 課題
1. B2 の「直すべき点」の各項目について、直しが「入った／不十分／入っていない／直しが誤り」のどれかを、短い理由とともに書いてください。直していない項目は、その扱いが文面（ノートの記録など）に書かれているかも見てください。
2. 差分の中の新しい文面に、形式文より強い言い方、形式文にないことを事実として書いた箇所、計算や参照の誤りがないかを見てください。あれば、場所と直し方の案を書いてください。
3. 全体の判定を 1 行で：直しで残ったずれ（あれば重要な順に）。
'''

def udiff(a_path, b_path, label, n=1):
    a = open(a_path, encoding='utf-8').read().split('\n')
    b = open(b_path, encoding='utf-8').read().split('\n')
    return '\n'.join(difflib.unified_diff(a, b, fromfile=label + '（直す前）', tofile=label + '（直した後）', lineterm='', n=n))

def xdiff(rng):
    old = load_workbook(BF + 'lean_verification_status.xlsx', read_only=True)['定理と証明']
    new = load_workbook('/home/claude/out/final76/lean_verification_status.xlsx', read_only=True)['定理と証明']
    o = list(old.iter_rows(min_row=rng[0], max_row=rng[1], values_only=True))
    n = list(new.iter_rows(min_row=rng[0], max_row=rng[1], values_only=True))
    out = []
    if o[0][0] != n[0][0]:
        out.append(f'【見出し（直す前）】{o[0][0]}\n【見出し（直した後）】{n[0][0]}')
    for ro, rn in zip(o, n):
        assert ro[1] == rn[1]
        for c, lab in [(2, '主張'), (3, '証明の要点')]:
            if ro[c] != rn[c]:
                out.append(f'【{rn[1]} の{lab}（直す前）】{ro[c]}\n【{rn[1]} の{lab}（直した後）】{rn[c]}')
    return '\n\n'.join(out)

for k, (lean, note, rng) in PARTS.items():
    t = open(R + f'prompt_B2_{k}.template.md', encoding='utf-8').read()
    i = t.index('## 入力 (1)'); j = t.index('## 入力 (3)')
    formal = t[i:j].replace('## 入力 (1)', '## 入力 (1)', 1).replace('## 入力 (2)', '## 入力 (2)', 1)
    b2 = open(R + f'agent_B2_{k}_output.md', encoding='utf-8').read().strip()
    ld = udiff(BF + f'{lean}.lean', f'/home/claude/leanwork/pagpkg/{lean}.lean', f'{lean}.lean')
    nd = udiff(BF + note, f'/home/claude/out185/{note}', note)
    xd = xdiff(rng)
    body = (HEAD + '\n' + formal.replace('★ は、前回の照合の後に足した文・文を変えた文です。\n', '')
            + '\n## 入力 (3)：B2 の出力の全文（原文のまま。行番号はノートの直す前の版のもの）\n\n' + b2 + '\n'
            + '\n## 入力 (4)：Lean ファイルの文面の差分（形式文は変えていない。冒頭の説明と docstring だけ）\n```diff\n' + ld + '\n```\n'
            + '\n## 入力 (5)：ノートの差分\n```diff\n' + nd + '\n```\n'
            + '\n## 入力 (6)：表（xlsx）の差分\n```\n' + xd + '\n```\n'
            + TASK)
    open(R + f'{D}/B3_{k}_input.md', 'w', encoding='utf-8').write(body)
    print(k, len(body))
