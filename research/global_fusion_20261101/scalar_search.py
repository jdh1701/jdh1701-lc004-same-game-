from fractions import Fraction as F
import json
from pathlib import Path
W=[1,0,3,3,15,33,105,297,879,2631,7833,23697,71385,216765,657849,2003151,6103743,18624693,56870385,173760513,531128349,1623881889,4965695331,15185222199,46435889601,141985777503,434087233947,1326879233787,4055050431933]
def nullspace(mat):
    a=[list(map(F,row)) for row in mat];piv=[];i=0;n=len(a[0])
    for j in range(n):
        k=next((k for k in range(i,len(a)) if a[k][j]),None)
        if k is None:continue
        a[i],a[k]=a[k],a[i];v=a[i][j];a[i]=[x/v for x in a[i]]
        for k in range(len(a)):
            if k!=i and a[k][j]:
                v=a[k][j];a[k]=[x-v*y for x,y in zip(a[k],a[i])]
        piv.append(j);i+=1
        if i==len(a):break
    free=[j for j in range(n) if j not in piv];basis=[]
    for j in free:
        v=[F(0)]*n;v[j]=1
        for i,p in enumerate(piv):v[p]=-a[i][j]
        basis.append(v)
    return basis
rec=[]
for d,maxr in [(0,13),(1,9),(2,6),(3,5),(4,4)]:
    for r in range(1,maxr+1):
        rows=[[F(n)**d0*W[n+j] for j in range(r+1) for d0 in range(d+1)] for n in range(26-r)]
        b=nullspace(rows);hold=[[F(n)**d0*W[n+j] for j in range(r+1) for d0 in range(d+1)] for n in range(26-r,29-r)]
        surviving=nullspace(rows+hold)
        # Empty nullspace rules out every recurrence in this finite template.
        rec.append({'order':r,'polynomial_degree':d,'training_nullity':len(b),'full_nullity_after_holdout':len(surviving)})
        print('rec',rec[-1],flush=True)
alg=[]
for dy,dz in [(1,13),(2,8),(3,6),(4,4),(5,3)]:
    pw=[[1]+[0]*28]
    for j in range(dy):pw.append([sum(pw[-1][i]*W[n-i] for i in range(n+1)) for n in range(29)])
    rows=[[pw[j][n-i] if n>=i else 0 for j in range(dy+1) for i in range(dz+1)] for n in range(26)]
    b=nullspace(rows)
    hold=[[pw[j][n-i] if n>=i else 0 for j in range(dy+1) for i in range(dz+1)] for n in range(26,29)]
    surviving=nullspace(rows+hold)
    alg.append({'degree_F':dy,'degree_z':dz,'training_nullity':len(b),'full_nullity_after_holdout':len(surviving)})
    print('alg',alg[-1],flush=True)
assert all(x['full_nullity_after_holdout']==0 for x in rec+alg)
res={'status':'VERIFIED-COMP','training':'coefficients 0..25','holdout':'26..28; surviving dimension computed from all 29 coefficients, allowing every linear combination of training basis vectors','recurrence_templates':rec,'algebraic_templates':alg,'scope':'Recurrences are required from n=0. Finite exact linear-algebra exclusions of specified templates; not a proof of nonrationality, nonalgebraicity, non-D-finiteness, or impossibility of an all-length formula.'}
Path(__file__).with_name('scalar-checks.json').write_text(json.dumps(res,indent=2)+'\n')
