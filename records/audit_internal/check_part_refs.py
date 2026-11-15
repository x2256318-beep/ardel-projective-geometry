# 「Part n の `名前`」の参照が、Part n のファイル（PAG 2.0 なら PAG(n+4).lean、付録 A の Part 2・3 なら PAG2・PAG3、Part 1 なら PAG.lean）に
# その名前の宣言があるかを確かめる。ないのに PAG n.lean にあるもの（ファイル番号を Part 番号として書いた疑い）を挙げる。
import json, re, sys, collections, openpyxl
D = [json.loads(l) for l in open('decls_all.jsonl') if l.strip()]
names = collections.defaultdict(set)
for d in D:
    names[d['module']].add(d['name'].split('.')[-1])
PAT = re.compile(r"(付録 A の )?Part (\d+)(?:（PAG(\d*)(?:\.lean)?）)?\s*の\s*`?([A-Za-z_][\w'₀-₉]*)`?")
def check(text, where):
    out = []
    for m in PAT.finditer(text):
        appA, n, pag, name = m.group(1), int(m.group(2)), m.group(3), m.group(4)
        if appA: mod = {1: 'PAG', 2: 'PAG2', 3: 'PAG3'}.get(n)
        elif n == 1 and name in names['PAG']: mod = 'PAG'
        else: mod = f'PAG{n + 4}'
        if mod is None: continue
        if name in names.get(mod, set()): continue
        alt = f'PAG{n}' if f'PAG{n}' in names else None
        hint = ''
        if alt and name in names[alt]: hint = f'（PAG{n}.lean にある：ファイル番号を Part 番号として書いた疑い）'
        elif not any(name in s for s in names.values()): hint = '（鎖に同名の宣言なし：Lean の名前でない語の可能性）'
        else:
            where_found = [m2 for m2, s in names.items() if name in s][:4]
            hint = f'（{",".join(where_found)} にある）'
        out.append(f'{where}: 「{m.group(0)}」→ {mod} に {name} なし {hint}')
    return out
res = []
for f in ['pag2_part249_idele_class_density.md', 'pag2_part250_resolution_emergence.md', 'pag2_part251_projective_limit.md', 'pag2_part252_hartley_gluing.md',
          'pag2_part253_primitive_operator.md', 'pag2_part254_full_gluing.md', 'pag2_part255_resolution_discrete_limit.md', 'pag2_part256_gluing_cross_term.md',
          'pag2_internal_audit_249_256.md', 'pag2_part257_preregistration.md']:
    res += check(open(f'/home/claude/out185/{f}', encoding='utf-8').read(), f)
res += check(open('/home/claude/out/final77/PAG2_handoff_internal_audit.md', encoding='utf-8').read(), 'handoff')
for k in range(253, 261):
    res += check(open(f'/home/claude/leanwork/pagpkg/PAG{k}.lean', encoding='utf-8').read(), f'PAG{k}.lean')
wb = openpyxl.load_workbook('/home/claude/out/final77/lean_verification_status.xlsx', read_only=True)
ws = wb['定理と証明']
for i, row in enumerate(ws.iter_rows(values_only=True), start=1):
    if row[0] and re.match(r'PAG2\.0-(249|25[0-6]) ', str(row[0])):
        for c, v in enumerate(row[1:5], start=2):
            if v: res += check(str(v), f'xlsx 行 {i} 列 {c}')
for r in res: print(r)
print('件数', len(res))
