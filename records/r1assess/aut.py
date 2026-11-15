# count permutations sigma of divisors of a such that D_s->D_s, E_s->E_{sigma(s)} extends to an automorphism of A_a
import itertools, sys
sys.argv=['x']; exec(open('uniq.py').read().split('for a,b in')[0])
for a in [2,3,4,5,6,8,9,10,12,15,16,18]:
    da=divs(a); g=[D(a,s) for s in da]+[E(a,s) for s in da]; dA=algdim(g); ok=[]
    for perm in itertools.permutations(da):
        sig=dict(zip(da,perm))
        pairs=[blk(D(a,s),D(a,s)) for s in da]+[blk(E(a,s),E(a,sig[s])) for s in da]
        if algdim(pairs)==dA: ok.append({s:sig[s] for s in da if sig[s]!=s})
    print(a,'dimA',dA,'#aut(fix D, permute E)',len(ok),ok); sys.stdout.flush()
