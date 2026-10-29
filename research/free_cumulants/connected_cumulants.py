"""kappa_s(q) = sum over NC-connected x (least NC coarsening is one block) of c(x) q^{|x|}; compare with cumulants.py."""
import sys, subprocess
from joins import run
from nc_factorization_check_lib import nc_closure
N = int(sys.argv[1])
out = subprocess.run([sys.executable, "cumulants.py"], capture_output=True, text=True).stdout.split("\n")
ref = {int(l.split(" ", 1)[0]): eval(l.split(" ", 1)[1]) for l in out if l.strip()}
for s in range(2, N + 1):
    poly = {}
    for x, c in run(s)[1].items():
        if len(set(nc_closure(list(x)))) == 1:
            k = max(x) + 1; poly[k] = poly.get(k, 0) + c
    lst = [poly.get(j, 0) for j in range(max(poly) + 1)] if poly else [0]
    while len(lst) > 1 and lst[-1] == 0: lst.pop()
    r = ref[s]
    while len(r) > 1 and r[-1] == 0: r = r[:-1]
    print(s, lst, "MATCH" if lst == r else f"DIFF vs {r}", flush=True)
