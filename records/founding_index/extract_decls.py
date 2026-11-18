# 索引に出る宣言ごとに、直前の docstring と、宣言の行から := までの形式文を取り出す
import re, sys, pathlib
idx = pathlib.Path(sys.argv[1]).read_text(encoding='utf-8')
lean_dir = pathlib.Path(sys.argv[2])
names = sorted(set(re.findall(r'`(PAG\.Part(\d+)\.([A-Za-z_][A-Za-z0-9_\'.]*))`', idx)), key=lambda t:(int(t[1]),t[2]))
kinds = r'(?:theorem|lemma|def|abbrev|structure|instance|class|inductive|noncomputable def|noncomputable abbrev|noncomputable instance)'
out=[]
for full, m, n in names:
    src = (lean_dir / f'PAG{m}.lean').read_text(encoding='utf-8')
    mt = re.search(rf'^\s*(?:@\[[^\]]*\]\s*)?(?:private\s+)?{kinds}\s+{re.escape(n)}(?=[\s:({{\[]|$)', src, re.M)
    start = mt.start()
    # docstring 直前
    pre = src[:start].rstrip()
    doc = ''
    if pre.endswith('-/'):
        j = pre.rfind('/--')
        k = pre.rfind('/-!')
        if j != -1 and j > k: doc = pre[j:]
    # := まで（最初の := ）または where
    rest = src[start:]
    is_def = not re.match(r'\s*(?:@\[[^\]]*\]\s*)?(?:private\s+)?(?:theorem|lemma)\b', rest)
    if is_def:
        # 定義は本体も含める（空行まで、最大 30 行）
        lines = rest.split('\n')
        acc = []
        for ln in lines[:30]:
            if acc and ln.strip() == '': break
            acc.append(ln)
        stmt = '\n'.join(acc)
    else:
        e = re.search(r':=', rest)
        stmt = rest[: e.start() + 2] if e else rest[:800]
    out.append(f'### {full}（PAG{m}.lean）\n```lean\n{doc}\n{stmt.strip()}\n```\n')
pathlib.Path(sys.argv[3]).write_text('\n'.join(out), encoding='utf-8')
print(len(out))
