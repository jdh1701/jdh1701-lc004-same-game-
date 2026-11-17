"""Reproduce the independently known length-27/28 totals with reversal DP."""
import sys,json,subprocess
from pathlib import Path
rows=[]
for n,expected in [(27,1326879233787),(28,4055050431933)]:
    p=subprocess.run([sys.argv[1],str(n),'8000000'],check=True,capture_output=True,text=True)
    r=json.loads(p.stdout);assert r['status']=='complete' and r['count']==expected;rows.append(r)
    print('PASS',n,r['count'],'peak',max(r['states']),flush=True)
Path(__file__).with_name('long-checks.json').write_text(json.dumps({'status':'VERIFIED-COMP','replays':rows},indent=2)+'\n')
