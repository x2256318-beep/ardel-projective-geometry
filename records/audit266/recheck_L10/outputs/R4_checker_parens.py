import sys
L = open(sys.argv[1], encoding='utf-8').read().split('\n')
def cnt(s):
    return dict(fw=(s.count('（'), s.count('）')), asc=(s.count('('), s.count(')')), kg=(s.count('「'), s.count('」')))
groups = {'PAG265 new':[159],'PAG266 src':[172],'PAG266 phase':[181],'PAG266 J0 (186+188+189)':[186,188,189],
 'EN overview':[207],'JP overview':[220],'handoff 1406':[233],'handoff 1098':[242],'handoff 12:48':[251],
 'handoff R3':[260],'handoff close':[261],'idx 2.4 a':[271],'idx 2.4 b':[275],'idx 2.8':[284],
 'note s1':[297],'note s2':[306],'note s4':[315],'note R2':[324],'note R3':[325],'ledger L10':list(range(366,379)),
 'ledger L9 scope add':[411,412,413],'ledger close summary':[382],'docstring':[428],
 'C: src':[459],'C: 462':[462],'C: phase':[481],'C: J0':[486,487,488],'C: label':[492]}
for k,v in groups.items():
    s=' '.join(L[i-1] for i in v)
    c=cnt(s); bad=[t for t,(a,b) in c.items() if a!=b]
    print(f"{k:28s} {c}  {'UNBALANCED '+str(bad) if bad else 'ok'}")
