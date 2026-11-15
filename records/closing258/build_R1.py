"""閉鎖条件 1：Part 254 の S18〜S50 の逆翻訳 A。入力は PAG258.lean の最終版から機械的に起こす（名前だけ中立化）。"""
import json, sys, re
sys.path.insert(0, '/home/claude/out/reaudit257')
import build_prompts_A2 as B
ren = json.load(open('/home/claude/out/audit254/rename_v2.json', encoding='utf-8'))
new = ['UA1_pullL_of_mem_Vprim', 'condPart_eq_map', 'ip_condPart', 'iSup_condPart', 'iSupIndep_condPart', 'UA1_mem_condPart', 'ipLim_ofL_Vprim']
for i, n in enumerate(new): ren[n] = f'S{51 + i}'
ren['condPart'] = 'Ω1'; ren['ipR'] = 'Ω2'
ren['ip_charU'] = 'R1'; ren['span_charU_eq_top'] = 'R2'; ren['eq_zero_of_ip_self'] = 'R3'
ths = B.theorems(B.PKG + 'PAG258.lean')
assert len(ths) == 57
tgt_names = [k for k, v in ren.items() if re.fullmatch(r'S(\d+)', v) and 18 <= int(v[1:]) <= 50]
ctx, tgt = [], []
for d in ths:
    s = B.neutralize(B.statement(d), ren)
    (tgt if d['name'] in tgt_names else ctx).append(s)
assert len(tgt) == 33, len(tgt)
deps = [B.neutralize(B.statement(d), ren) for d in B.theorems(B.PKG + 'PAG257.lean') if d['name'] in ('ip_charU', 'span_charU_eq_top', 'eq_zero_of_ip_self')]
defs = open('/home/claude/out/audit254/defs_neutral_v2.lean', encoding='utf-8').read().strip()
defs += '''

-- 以下は S51〜S57 で使う定義
noncomputable def Ω1 (N : ℕ) [NeZero N] (q : ℕ) : Submodule ℂ ((ZMod N)ˣ → ℂ) :=
  Submodule.span ℂ (Set.range fun χ : {χ : DirichletCharacter ℂ N // χ.conductor = q} => Ψ4 χ.1)

noncomputable def Ω2 (f : (ZMod N)ˣ → ℂ) : ((ZMod N)ˣ → ℂ) →ₗ[ℂ] ℂ where
  toFun := Ψ5 f
  -- map_add'・map_smul' の証明は省略'''
gloss = open('/home/claude/out/audit254/prompt_A.md', encoding='utf-8').read()
gloss = gloss[gloss.index('## Mathlib の前提'):gloss.index('## 入力 (1)')]
gloss = '\n' + gloss.strip() + ' `iSupIndep F` は部分空間の族 F が独立。`⨆ q, F q` は族の和。`Module.DirectLimit` は加群の帰納極限（代数的な直極限、完備化はしない）。\n'
head = B.HEAD.replace('- ツールは一切使わないでください（ファイル、シェル、検索、エージェントの起動もしない）。', '- このファイル 1 つを Read で読むほかは、ツールを使わないでください（シェル、検索、エージェントの起動もしない）。')
body = (head + gloss
  + '\n## 入力 (1)：定義（内容は原文のまま、名前だけ置き換えた。線形写像の証明の義務と、定義の中の証明の項は省いた。ファイルではすべてコンパイル済み）\n' + B.block([defs])
  + '\n## 入力 (2)：文脈として示す文（判定の対象ではない。すべてコンパイル済みで sorry なし）\n前のファイルの文：\n' + B.block(deps)
  + '同じファイルの文（S1〜S17、S51〜S57）：\n' + B.block(ctx)
  + '\n## 入力 (3)：判定の対象の文（S18〜S50。すべてコンパイル済みで sorry なし、公理は標準の 3 つ以内）\n' + B.block(tgt)
  + B.TASK.format(targets='S18〜S50'))
B.check_no_leak(body, ['UA1', 'condPart', 'ipR', 'Vprim', 'charU', 'ipLim', 'ofL', 'pullL', 'TopL', 'phaseA1', 'rootNum', 'Uinf'])
open('R1_input.md', 'w', encoding='utf-8').write(body)
json.dump(ren, open('R1_rename.json', 'w', encoding='utf-8'), ensure_ascii=False, indent=1)
print(len(body))
