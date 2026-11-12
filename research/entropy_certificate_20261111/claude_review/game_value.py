"""Claude review, 2026-11-12. Worst-case mean drift of the H=9 control table (prefix9-1.txt)
over ALL potentials, as a mean-payoff game: an adversary picks the next-to-last base color b per state
(as the certificate requires every b to satisfy the drift inequality), the input letter is drawn from the
law, and reward is the base-length change r. A potential p with every row's expected drift < 0 exists
iff this game value (max mean drift) is negative. Relative value iteration with tau=1/2 aperiodicity mix.
Two law families: 'fixed' = (1+e,1,1) on the certificate's favored colors; 'free' = favored color chosen
per (state,b) to minimize drift. Standard library + NumPy only. Discovery-grade numerics, not a certificate.
"""
import numpy as np, pathlib, json
d = pathlib.Path(__file__).resolve().parent.parent
raw = (d/'prefix9-1.txt').read_text().splitlines()
H, N = map(int, raw[0].split())
J = np.zeros((N,2,3), int); R = np.zeros((N,2,3))
for i,row in enumerate(raw[1:]):
    f=row.split(); k=int(f[1]); nums=list(map(int,f[2+k:]))
    for e in range(6): J[i,e//3,e%3]=nums[2*e]; R[i,e//3,e%3]=nums[2*e+1]
cert=(d/'tilted10-9.certificate.txt').read_text().splitlines()
FAV=np.array([[int(x) for x in l.split()[2:4]] for l in cert[1:N+1]])
def value(eps, free, tau=0.5, iters=60000):
    if not free:
        W=np.ones((N,2,3))
        for b in (0,1): W[np.arange(N),b,FAV[:,b]]=1+eps
        W/=W.sum(2,keepdims=True)
    h=np.zeros(N); g=None
    for t in range(iters):
        V=R+h[J]
        q=((V.sum(2)[...,None]+eps*V).min(2)/(3+eps)).max(1) if free else (W*V).sum(2).max(1)
        q=tau*q+(1-tau)*h; gn=q[0]-h[0]; h=q-q[0]
        if g is not None and t>2000 and abs(gn-g)<1e-13: break
        g=gn
    return g/tau
def rate(e):
    p=np.array([1+e,1,1])/(3+e); return float(np.exp(-(p*np.log(p)).sum()))
out={'certificate_bias_1_over_9_fixed': value(1/9,False),
     'certified_delta_for_comparison': 3041932/2800000000,
     'uniform_fixed': value(0.0,False), 'uniform_free': value(0.0,True)}
for free in (False,True):
    lo,hi=0.0,0.1112
    for _ in range(20):
        m=(lo+hi)/2; (lo,hi)=(m,hi) if value(m,free)>0 else (lo,m)
    out['threshold_'+('free' if free else 'fixed')]=[lo,hi]
    out['rate_ceiling_'+('free' if free else 'fixed')]=rate(hi)
print(json.dumps(out,indent=1))
