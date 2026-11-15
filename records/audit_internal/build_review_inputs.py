# 照合者の入力：グループごとに targets.md（対象の全文と候補の名前）、candidates.md（候補の全文）、README.md（依頼文）。
import json, re, os
S = json.load(open('statements_all.json')); IDX, CTX = S['index'], S['ctx']
SL = json.load(open('shortlist_k8.json'))
AUTO = re.compile(r'(congr_simp|\.eq_\d+$|\.eq_def$)')
def key_of(declname, module):
    short = re.sub(r'^PAG\.Part\d+\.', '', declname)
    k = f'{module}::{short}'
    if k in IDX: return k
    last = short.split('.')[-1]
    for kk in IDX:
        if kk.startswith(module + '::') and kk.split('::')[1].split('.')[-1] == last:
            return kk
    return None
GROUPS = {'R1': ['PAG253', 'PAG254'], 'R2': ['PAG255', 'PAG256'], 'R3': ['PAG257'], 'R4': ['PAG258'], 'R5': ['PAG259', 'PAG260']}
PART = lambda m: int(m[3:]) - 4
summary = {}
for g, mods in GROUPS.items():
    d = f'inbox_{g}'; os.makedirs(d, exist_ok=True)
    tg = [r for r in SL if r['module'] in mods and not AUTO.search(r['target'])]
    cands = {}
    with open(f'{d}/targets.md', 'w', encoding='utf-8') as out:
        for m in mods:
            out.write(f'\n######## {m}.lean（Part {PART(m)}）\n-- 文脈（open・variable・namespace の行の写し）\n' + '\n'.join(CTX[m]) + '\n')
            for r in [r for r in tg if r['module'] == m]:
                k = key_of(r['target'], m)
                out.write(f"\n### 対象 {k or r['target']}（{r['kind']}）\n")
                out.write((IDX[k]['text'] if k else '（ソースに独立の宣言がない：構造体のフィールドなど自動で作られたもの）') + '\n')
                names = []
                for c in r['cands']:
                    if AUTO.search(c['name']): continue
                    ck = key_of(c['name'], c['module'])
                    if ck: names.append(ck); cands[ck] = c['module']
                out.write('候補（型に現れる定数の近さの順。機械的に選んだもので、判定ではない）：' + '、'.join(names) + '\n')
    with open(f'{d}/candidates.md', 'w', encoding='utf-8') as out:
        for m in sorted(set(cands.values()), key=lambda x: int(x[3:])):
            out.write(f'\n######## {m}.lean\n-- 文脈（open・variable・namespace の行の写し）\n' + '\n'.join(CTX[m]) + '\n')
            for ck in sorted([c for c in cands if cands[c] == m], key=lambda c: IDX[c]['line']):
                out.write(f"\n### {ck}（{IDX[ck]['kind']}、{IDX[ck]['line']} 行）\n{IDX[ck]['text']}\n")
    summary[g] = (len(tg), len(cands), os.path.getsize(f'{d}/targets.md'), os.path.getsize(f'{d}/candidates.md'))
print(summary)
