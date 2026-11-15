# 内部照合の候補選び：Part 249〜256（PAG253〜260）の各宣言について、それより前の PAG の宣言から
# 「型に現れる定数（PAG の定義は値の定数まで展開）」の TF-IDF の近さで上位 k 個を選ぶ。
import json, re, math, collections, sys
K = int(sys.argv[1]) if len(sys.argv) > 1 else 8
D = [json.loads(l) for l in open('decls_all.jsonl') if l.strip()]
def modnum(m):
    mm = re.match(r'PAG(\d+)$', m); return int(mm.group(1)) if mm else 0
AUTO = re.compile(r'\.(noConfusion|noConfusionType|recOn|casesOn|ctorIdx|sizeOf_spec|injEq|inj|rec|mk|decEq|brecOn|below|ibelow)$')
def skip(d):
    last = d['name'].split('.')[-1]
    return d['kind'] not in ('thm', 'def') or AUTO.search(d['name']) or last.startswith('inst') or last.startswith('_')
byname = {d['name']: d for d in D}
pag = set(byname)
# PAG の定義を、値に現れる PAG 以外の定数まで展開（推移的）
memo = {}
def expand(c, depth=0):
    if c in memo: return memo[c]
    if c not in pag or byname[c]['kind'] != 'def' or depth > 12:
        memo[c] = {c}; return memo[c]
    memo[c] = {c}
    out = {c}
    for v in byname[c]['value']:
        out |= expand(v, depth + 1)
    memo[c] = out
    return out
def tokens(d):
    s = set()
    for c in d['type']:
        s |= expand(c)
    if d['kind'] == 'def':
        for c in d['value']:
            s |= expand(c)
    return s
docs = {d['name']: tokens(d) for d in D if not skip(d)}
N = len(docs)
df = collections.Counter(t for s in docs.values() for t in s)
idf = {t: math.log(N / df[t]) for t in df}
COMMON = {t for t in df if df[t] > 0.3 * N}
def vec(s):
    v = {t: idf[t] for t in s if t not in COMMON}
    n = math.sqrt(sum(x * x for x in v.values())) or 1.0
    return {t: x / n for t, x in v.items()}
V = {n: vec(s) for n, s in docs.items()}
def cos(a, b):
    if len(a) > len(b): a, b = b, a
    return sum(x * b.get(t, 0.0) for t, x in a.items())
targets = [n for n in docs if modnum(byname[n]['module']) >= 253]
res = []
for t in sorted(targets, key=lambda n: (modnum(byname[n]['module']), n)):
    mt = modnum(byname[t]['module']); kt = byname[t]['kind']
    cands = []
    for s in docs:
        ms = modnum(byname[s]['module'])
        if (ms == 0 and byname[s]['module'] != 'PAG') or ms >= mt or byname[s]['kind'] != kt: continue
        c = cos(V[t], V[s])
        if c > 0: cands.append((c, s))
    cands.sort(reverse=True)
    res.append({'target': t, 'module': byname[t]['module'], 'kind': kt,
                'cands': [{'name': s, 'module': byname[s]['module'], 'score': round(c, 3)} for c, s in cands[:K]]})
json.dump(res, open('shortlist_all.json', 'w'), ensure_ascii=False, indent=1)
print('対象', len(targets), '件、候補の組', sum(len(r['cands']) for r in res))
# 確認：既知の重複が上位に入っているか
for t, s in [('PAG.Part260.gaussSum_prodChar', 'PAG.Part193.gaussSum_mul_coprime'),
             ('PAG.Part260.isPrimitive_prodChar', 'PAG.Part194.isPrimitive_mul')]:
    r = next(r for r in res if r['target'] == t)
    names = [c['name'] for c in r['cands']]
    print(t, '→', s, 'の順位：', names.index(s) + 1 if s in names else '圏外', names[:4])
