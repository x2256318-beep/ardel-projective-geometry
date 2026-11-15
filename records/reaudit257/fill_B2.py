#!/usr/bin/env python3
"""A2 の出力（原文のまま保存したファイル）を B2 の依頼文に差し込み、入力ファイルを作る。"""
import sys
D = open('/home/claude/out/reaudit257/inbox_dir.txt').read().strip()
old = '- ツールは一切使わないでください（ファイル、シェル、検索、エージェントの起動もしない）。'
new = '- この入力ファイルを Read で 1 回読んだあとは、ツールを一切使わないでください（ほかのファイル、シェル、検索、Web、エージェントの起動もしない）。この入力は長いので、Read が途中で切れたら、同じファイルの続き（offset を指定）を読むことだけは許します。'
for k in sys.argv[1:]:
    t = open(f'/home/claude/out/reaudit257/prompt_B2_{k}.template.md', encoding='utf-8').read()
    a2 = open(f'/home/claude/out/reaudit257/agent_A2_{k}_output.md', encoding='utf-8').read().strip()
    assert t.count('{{A2_OUTPUT}}') == 1 and t.count(old) == 1
    t = t.replace('{{A2_OUTPUT}}', a2).replace(old, new)
    t = t.replace('最後に、使ったツール（使っていなければ「なし」）を書いてください。', '最後に、使ったツール（入力ファイルの Read 以外に使っていなければ「Read のみ（回数）」）を書いてください。')
    open(f'/home/claude/out/reaudit257/{D}/B2_{k}_input.md', 'w', encoding='utf-8').write(t)
    print(k, len(t))
