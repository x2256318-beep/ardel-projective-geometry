# 材料索引に出る完全修飾名 PAG.PartM.name を取り出し、PAGM.lean に宣言があるか確かめる
import re, sys, pathlib
idx = pathlib.Path(sys.argv[1]).read_text(encoding='utf-8')
lean_dir = pathlib.Path(sys.argv[2])
names = sorted(set(re.findall(r'`(PAG\.Part(\d+)\.([A-Za-z_][A-Za-z0-9_\'.]*))`', idx)))
kinds = r'(?:theorem|lemma|def|abbrev|structure|instance|class|inductive|noncomputable def|noncomputable abbrev|noncomputable instance)'
ok = bad = 0
for full, m, n in names:
    src = (lean_dir / f'PAG{m}.lean').read_text(encoding='utf-8')
    if not re.search(rf'namespace PAG\.Part{m}\b', src):
        print('NS?', full); bad += 1; continue
    if re.search(rf'^\s*(?:@\[[^\]]*\]\s*)?(?:private\s+)?{kinds}\s+{re.escape(n)}(?=[\s:({{\[]|$)', src, re.M):
        print('ok ', full); ok += 1
    else:
        print('NO ', full); bad += 1
print(f'合計 {len(names)} 件、確認 {ok}、見つからない {bad}')
