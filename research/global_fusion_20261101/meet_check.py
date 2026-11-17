"""Reproducible replay of the separate half-word incidence algorithm."""
import json,subprocess,sys
from pathlib import Path
known=[1,0,3,3,15,33,105,297,879,2631,7833,23697,71385,216765,657849,2003151,6103743,18624693,56870385,173760513,531128349,1623881889,4965695331,15185222199,46435889601,141985777503,434087233947,1326879233787,4055050431933]
rows=[]
for n in range(29):
    p=subprocess.run([sys.argv[1],str(n)],check=True,capture_output=True,text=True)
    r=json.loads(p.stdout);assert r['status']=='complete' and r['count']==known[n];rows.append(r)
result={'status':'VERIFIED-COMP','method':'explicit half-word support incidence, independent of forward horizon DP','replays':rows,'scope':'N<=25 match OEIS; N=26 independently matches forward DP; N=27,28 computed with the half-word algorithm. No closed scalar all-length formula.'}
Path(__file__).with_name('meet-checks.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({'status':result['status'],'replay_count':len(rows),'last':rows[-1]},indent=2))
