# 全 PAG ファイルの宣言を文にする（定理は証明を除く、定義は全文、コメントを除く）。各ファイルの variable・open も付ける。
import sys, re, json, os
sys.path.insert(0, '/home/claude/out/reaudit257')
import leanparse
SRC = '/home/claude/leanwork/pagpkg'
files = sorted([f for f in os.listdir(SRC) if re.match(r'PAG\d+\.lean$', f)], key=lambda f: int(f[3:-5]))
index = {}   # (file, name) -> statement
ctx = {}
for f in files:
    path = os.path.join(SRC, f)
    s = open(path, encoding='utf-8').read()
    ctxl = [l for l in s.split('\n') if re.match(r'^(open |variable |namespace |section|end )', l)]
    ctx[f[:-5]] = ctxl
    _, decls = leanparse.parse(path)
    for d in decls:
        st = leanparse.statement(d)
        index[f[:-5] + '::' + d['name']] = {'kind': d['kind'], 'line': d['line'], 'text': st}
json.dump({'index': index, 'ctx': ctx}, open('statements_all.json', 'w'), ensure_ascii=False)
# 読み物の形（照合者が Grep で探す用）
with open('statements_all.txt', 'w', encoding='utf-8') as out:
    for f in files:
        m = f[:-5]
        out.write(f'\n######## {m}.lean\n')
        out.write('-- 文脈（この行は open・variable・namespace の写し）\n' + '\n'.join(ctx[m]) + '\n')
        for k, v in index.items():
            if k.startswith(m + '::'):
                out.write(f'\n### {m}::{k.split("::",1)[1]}（{v["kind"]}、{v["line"]} 行）\n{v["text"]}\n')
print(len(files), 'files', len(index), 'decls', os.path.getsize('statements_all.txt'), 'bytes')
