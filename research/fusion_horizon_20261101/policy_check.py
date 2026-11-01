"""Finite comparison of eight valid representative policies; not a speed theorem."""
import json,subprocess,sys
from pathlib import Path
names=['lexicographic minimum','lexicographic maximum','minimum total successor cardinality','minimum maximum successor cardinality','maximum total successor cardinality','maximum maximum successor cardinality','minimum total successor stack length','maximum total successor stack length']
rows=[]
for p,name in enumerate(names):
    r=json.loads(subprocess.check_output([sys.argv[1],'22','2000000',str(p)],text=True,stderr=subprocess.DEVNULL));assert r['count']==4965695331
    r['policy']=name;r['peak_states']=max(r['states']);rows.append(r)
greedy=[]
for n,x in [(14,657849),(18,56870385),(22,4965695331)]:
    r=json.loads(subprocess.check_output([sys.argv[2],str(n)],text=True,stderr=subprocess.DEVNULL));assert r['count']==x
    r['peak_states']=max(r['states']);greedy.append(r)
known=[1,0,3,3,15,33,105,297,879,2631,7833,23697,71385,216765,657849,2003151,6103743,18624693,56870385]
meet=[]
for n,x in enumerate(known):
    r=json.loads(subprocess.check_output([sys.argv[3],str(n)],text=True,stderr=subprocess.DEVNULL));assert r['count']==x;meet.append(r)
result={'status':'VERIFIED-COMP','n':22,'policies':rows,'greedy_replays':greedy,'smaller_right_replays':meet,'scope':'All tested policies agree on totals; their state counts differ. Finite comparison only, no claim about asymptotically optimal representatives.'}
Path(__file__).with_name('policy-checks.json').write_text(json.dumps(result,indent=2)+'\n')
print([(r['policy'],r['peak_states']) for r in rows]);print('greedy',[(r['n'],r['peak_states']) for r in greedy]);print('smaller-right replays:',len(meet))
