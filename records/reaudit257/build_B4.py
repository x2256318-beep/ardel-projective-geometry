#!/usr/bin/env python3
"""B4（第 2 回の直しの照合）の入力を作る。4 Part を 1 つのファイルにまとめる。第 1 回の直しの後の状態は、
fix_round2.py の置き換えを逆にたどって作る（その状態は保存していなかったため）。"""
import difflib, re, sys, os
sys.path.insert(0, '/home/claude/out/reaudit257/fixes')
R = '/home/claude/out/reaudit257/'
D = open(R + 'inbox_dir.txt').read().strip()
src = open(R + 'fixes/fix_round2.py', encoding='utf-8').read()
# fix_round2.py の apply(...) の呼び出しを、置き換えの組の一覧として取り出す
ns = {}
calls = []
def apply(p, reps):
    calls.append((p, reps))
code = src.split("def apply(p, reps):")[0] + "\n" + src.split("print('ok')")[0].split("open(p, 'w', encoding='utf-8').write(s)\n", 1)[1]
exec(code, {'apply': apply})
os.makedirs(R + 'round1_state', exist_ok=True)
diffs = {}
for p, reps in calls:
    cur = open(p, encoding='utf-8').read()
    prev = cur
    for a, b in reversed(reps):
        assert prev.count(b) == 1, (p, b[:40])
        prev = prev.replace(b, a)
    name = p.split('/')[-1]
    open(R + 'round1_state/' + name, 'w', encoding='utf-8').write(prev)
    d = '\n'.join(difflib.unified_diff(prev.split('\n'), cur.split('\n'), fromfile=name + '（第 1 回の直しの後）', tofile=name + '（第 2 回の直しの後）', lineterm='', n=1))
    diffs[name] = d
PARTS = {'252': ['PAG256.lean', 'pag2_part252_hartley_gluing.md'], '254': ['PAG258.lean', 'pag2_part254_full_gluing.md'],
         '255': ['PAG259.lean', 'pag2_part255_resolution_discrete_limit.md'], '256': ['PAG260.lean', 'pag2_part256_gluing_cross_term.md']}
XL = {'256': '【rootNum_prodChar_ne_mul の主張（第 1 回の後）】…（存在の文。条件を満たす 2 組のどちらでも成り立つ。比の値 ∓i は文にない）\n【rootNum_prodChar_ne_mul の主張（第 2 回の後）】…（Lean の文は存在だけ。条件を満たす 2 組のどちらでも成り立つことは手計算と再照合 A2 による。比の値 ∓i は文にない）'}
HEAD = '''あなたは独立の照合者です。ある Lean 4（Mathlib）の形式化について、照合者 B3 が文面の直しの残りを指摘し、構築者がもう一度文面を直しました（第 2 回の直し）。4 つのファイル（Part 252・254・255・256）について、第 2 回の直しが正しく入ったかを、形式文と突き合わせて判定してください。

## 守ってほしいこと
- この入力ファイルを Read で読んだあとは、ツールを一切使わないでください（ほかのファイル、シェル、検索、Web、エージェントの起動もしない）。長くて 1 回で読み切れないときは、同じファイルの続き（offset を指定）を読むことだけ許します。
- 定義名・定理名は意味の根拠にしないでください。著者の解釈の言葉は「読み」と明示されていれば許容です。
- 判断ごとに確信度（高・中・低）を付けてください。回答は日本語で、各 Part 500 字程度、全体で 2,500 字までにまとめてください。最後に Read の回数を書いてください。

## 課題（各 Part について）
1. B3 が挙げた残りのずれのそれぞれが、第 2 回の直しで「入った／不十分／入っていない」か。直していないものの扱いが記録されているか。
2. 第 2 回の直しの新しい文面に、形式文より強い言い方や新しい誤りがないか。
3. 1 行の判定。
'''
body = HEAD
for k, (lean, note) in PARTS.items():
    t = open(R + f'prompt_B2_{k}.template.md', encoding='utf-8').read()
    formal = t[t.index('## 入力 (1)'):t.index('## 入力 (3)')].replace('★ は、前回の照合の後に足した文・文を変えた文です。\n', '')
    formal = formal.replace('## 入力 (1)', f'### Part {k} の入力 (1)').replace('## 入力 (2)', f'### Part {k} の入力 (2)')
    b3 = open(R + f'agent_B3_{k}_output.md', encoding='utf-8').read().strip()
    body += f'\n\n## Part {k}\n\n' + formal + f'\n### Part {k} の入力 (3)：B3 の出力の全文（原文のまま）\n\n' + b3 + '\n'
    body += f'\n### Part {k} の入力 (4)：第 2 回の直しの差分（Lean の文面とノート。形式文は変えていない）\n```diff\n' + diffs[lean] + '\n\n' + diffs[note] + '\n```\n'
    if k in XL:
        body += f'\n### Part {k} の入力 (5)：表（xlsx）の差分\n```\n' + XL[k] + '\n```\n'
open(R + f'{D}/B4_all_input.md', 'w', encoding='utf-8').write(body)
print(len(body))
