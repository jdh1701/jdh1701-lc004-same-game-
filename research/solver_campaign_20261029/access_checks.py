"""Bounded, archived access checks; no authentication or terms acceptance."""
import concurrent.futures,datetime,json,time
from pathlib import Path
import urllib.request, urllib.parse, urllib.error
root=Path(__file__).parent/'access';root.mkdir(exist_ok=True)
queries={
 'openalex_lehner':('GET','https://api.openalex.org/works/https://doi.org/10.1006/eujc.2002.0619',{}),
 'openalex_linked':('GET','https://api.openalex.org/works',{'params':{'search':'linked diagrams connected partitions Stein','per-page':5}}),
 'openalex_touchard':('GET','https://api.openalex.org/works',{'params':{'search':'Touchard configurations fractions continues','per-page':5}}),
 'sage_tos':('GET','https://sagecell.sagemath.org/tos.html',{}),
 'sage_service':('POST','https://sagecell.sagemath.org/service',{'data':{'code':"R.<k> = PolynomialRing(QQ)\nf=(38*k^6+694*k^5+4025*k^4+6670*k^3-5593*k^2-9434*k+6840)/(360*(k+8))\nprint(version())\nprint('leading',f.numerator().leading_coefficient()/f.denominator().leading_coefficient())\nprint('residue',((k+8)*f)(-8))"}})
}
def fetch(item):
 name,(method,url,kw)=item;start=time.time();out={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'url':url,'method':method,'parameters':kw}
 try:
  query=urllib.parse.urlencode(kw.get('params',{})); target=url+('?' + query if query else ''); data=urllib.parse.urlencode(kw['data']).encode() if 'data' in kw else None
  req=urllib.request.Request(target,data=data,method=method)
  with urllib.request.urlopen(req,timeout=20) as r: out.update(status=r.status,body=r.read().decode(errors='replace'))
 except Exception as e:out['error']=repr(e)
 out['seconds']=time.time()-start
 (root/(name+'.json')).write_text(json.dumps(out,indent=2)+'\n')
 print(name,out.get('status'),out.get('error',''),flush=True)
with concurrent.futures.ThreadPoolExecutor(max_workers=5) as ex:list(ex.map(fetch,queries.items()))
