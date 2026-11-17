"""Exact local compatibility and join tables, generated from original certificates."""
from pathlib import Path
from itertools import combinations
import json,sys
HERE=Path(__file__).resolve().parent;ROOT=HERE.parents[1]
sys.path.insert(0,str(ROOT/'research/ten_attacks_20261030'))
from core import catalogue,blocks,crossing,join

cats={n:catalogue(n) for n in (5,6)}
assert [len(cats[n]) for n in (5,6)]==[5,8]
tables={}
for n in (5,6):
    table=[(0,0)]*(1<<(5+n))
    for left in combinations(range(5+n),5):
        right=tuple(i for i in range(5+n) if i not in left)
        opts=[[tuple(tuple(g[i] for i in B) for B in blocks(c)) for c in cats[len(g)]] for g in (left,right)]
        mask=sum(1<<i for i in left);allowed=0
        for x,A in enumerate(opts[0]):
            for y,B in enumerate(opts[1]):
                if not any(crossing(a,b) for a in A for b in B):allowed|=1<<(x*len(cats[n])+y)
        table[mask]=(allowed,int(crossing(left,right)))
    tables[n]=table
states=[tuple(range(6))]
for c in cats[6]:
    for q in list(states):
        s=join(q,c)
        if s not in states:states.append(s)
trans=[[states.index(join(q,c)) for c in cats[6]] for q in states]
top=states.index((0,)*6)
with (HERE/'tables.txt').open('w') as f:
    f.write(f'{len(states)} {top}\n')
    for row in trans:f.write(' '.join(map(str,row))+'\n')
    for n in (5,6):
        for allowed,cross in tables[n]:f.write(f'{allowed} {cross}\n')
out=dict(status='VERIFIED-COMP',catalogues={n:cats[n] for n in cats},six_join_states=states,six_join_transitions=trans,six_top=top,table_rows=[len(tables[n]) for n in (5,6)])
(HERE/'local-tables.json').write_text(json.dumps(out,indent=2)+'\n')
print('catalogue sizes 5,8; six join states',len(states),'top',top)
