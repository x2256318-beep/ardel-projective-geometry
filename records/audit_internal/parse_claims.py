# 照合者の表を読み、対象・判定・前の宣言（Lean の完全な名前に直す）を取り出す。
import re, json, collections
D = [json.loads(l) for l in open('decls.jsonl') if l.strip()]
bymod = collections.defaultdict(list)
for d in D: bymod[d['module']].append(d)
def resolve(mod, short):
    short = short.strip().strip('`')
    cands = [d for d in bymod.get(mod, []) if d['name'] == short or d['name'].endswith('.' + short)]
    if len(cands) == 1: return cands[0]['name'], cands[0]['kind']
    # 名前空間の直下を優先
    exact = [d for d in cands if d['name'].split('.')[-1] == short.split('.')[-1] and d['name'].count('.') == min(c['name'].count('.') for c in cands)]
    if exact: return exact[0]['name'], exact[0]['kind']
    return None, None
GROUP_MODS = {'R1': ['PAG253', 'PAG254'], 'R2': ['PAG255', 'PAG256'], 'R3': ['PAG257'], 'R4': ['PAG258'], 'R5': ['PAG259', 'PAG260']}
TOK = re.compile(r"(PAG\d*)::([A-Za-z_][\w\.'₀-₉]*)")
claims = []
for g, mods in GROUP_MODS.items():
    txt = open(f'outputs/{g}_output.md', encoding='utf-8').read()
    for line in txt.split('\n'):
        if not line.startswith('|') or line.startswith('|---') or '判定' in line.split('|')[2:3][0:1] and False: continue
        cells = [c.strip() for c in line.strip().strip('|').split('|')]
        if len(cells) < 5 or cells[0] in ('宣言',) or set(cells[0]) <= set('-: '): continue
        tname = cells[0]
        m = TOK.search(tname)
        if m: tmod, tshort = m.group(1), m.group(2)
        else:
            tmod, tshort = mods[0], re.sub(r'（.*?）', '', tname).strip()
            if len(mods) > 1:
                for mm in mods:
                    if resolve(mm, tshort)[0]: tmod = mm; break
        tshort = re.sub(r'（.*?）', '', tshort).strip()
        tfull, tkind = resolve(tmod, tshort)
        v = re.match(r'\s*([ABCD])', cells[1])
        verdict = v.group(1) if v else '?'
        gen = '一般化' in cells[1] or '強めた' in cells[1] or '一般化' in cells[2]
        earlier = []
        for mm in TOK.finditer(cells[2]):
            emod, eshort = mm.group(1), mm.group(2)
            if emod == 'PAG1': emod = 'PAG'
            efull, ekind = resolve(emod, eshort)
            earlier.append({'ref': f'{emod}::{eshort}', 'full': efull, 'kind': ekind})
        claims.append({'group': g, 'target_ref': f'{tmod}::{tshort}', 'target': tfull, 'kind': tkind,
                       'verdict': verdict, 'generalization': gen, 'earlier': earlier,
                       'reason': cells[3], 'conf': cells[4]})
json.dump(claims, open('claims.json', 'w'), ensure_ascii=False, indent=1)
c = collections.Counter((x['group'], x['verdict']) for x in claims)
print(sorted(c.items()))
print('unresolved targets:', [x['target_ref'] for x in claims if not x['target']])
print('unresolved earlier:', sorted({e['ref'] for x in claims for e in x['earlier'] if not e['full']}))
