"""Exact residual-language discrimination, not a general counting solution."""
from pathlib import Path
from itertools import product
from functools import lru_cache
import json, sys
import sympy as sp
from z3 import Solver, Int, And, Or, Not, If, Sum, sat, get_version_string
sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from rigid_face_geometry_check import wins
from heavy_greedy_obstruction import bfs

ROOT = Path(__file__).resolve().parent


def modular_minor(matrix, prime=101):
    a = [list(map(int, row)) for row in matrix]
    ids = list(range(len(a)))
    rows, cols, det = [], [], 1
    for col in range(len(a[0])):
        pos = next((j for j in range(len(rows),len(a)) if a[j][col] % prime), None)
        if pos is None:
            continue
        r = len(rows)
        a[r],a[pos] = a[pos],a[r]
        ids[r],ids[pos] = ids[pos],ids[r]
        pivot = a[r][col] % prime
        rows.append(ids[r]); cols.append(col); det = det*pivot % prime
        inv = pow(pivot,-1,prime)
        for j in range(r+1,len(a)):
            factor = a[j][col]*inv % prime
            if factor:
                a[j] = [(v-factor*w)%prime for v,w in zip(a[j],a[r])]
    # Determinant of the original minor in pivot-selection order.
    minor = sp.Matrix([[matrix[i][j] for j in cols] for i in rows])
    independent = int(sp.polys.matrices.DomainMatrix.from_Matrix(minor).det()) % prime
    assert independent == det != 0
    return dict(prime=prime, rows=rows, columns=cols, determinant_mod_prime=det)


def hankel(q,depth):
    words = [w for n in range(depth+1) for w in product(range(q),repeat=n)]
    matrix = [[int(wins(u+v)) for v in words] for u in words]
    rank = sp.polys.matrices.DomainMatrix.from_Matrix(sp.Matrix(matrix)).rank()
    certificate = modular_minor(matrix)
    assert len(certificate['rows']) == rank
    return dict(q=q,depth=depth,dimension=len(words),rational_rank=rank,
                minor_certificate=certificate)


def membership(xs,table):
    return Or([And([x==a for x,a in zip(xs,w)]) for w in table])


def features(xs):
    return [xs[0],xs[-1]] + [Sum([If(x==a,1,0) for x in xs]) for a in range(3)] + [
        1+Sum([If(xs[i]!=xs[i-1],1,0) for i in range(1,len(xs))]),
        Sum([If(And(Or(i==0,xs[i]!=xs[i-1]),xs[i]==xs[i+1]),1,0)
             for i in range(len(xs)-1)])]


def summary_collision():
    checks=[]
    for n in range(2,7):
        words=list(product(range(3),repeat=n))
        winning=[w for w in words if wins(w)]
        extended=[w for w in words if wins(w+(0,))]
        x=[Int('x'+str(i)) for i in range(n)]
        y=[Int('y'+str(i)) for i in range(n)]
        solver=Solver(); solver.set(timeout=10000)
        solver.add(*[And(a>=0,a<3) for a in x+y])
        solver.add(*[a==b for a,b in zip(features(x),features(y))])
        solver.add(Not(membership(x,winning)),Not(membership(y,winning)),
                   membership(x,extended),Not(membership(y,extended)))
        status=solver.check();checks.append(dict(n=n,status=str(status)))
        if status==sat:
            model=solver.model()
            a=tuple(model.eval(v).as_long() for v in x)
            b=tuple(model.eval(v).as_long() for v in y)
            assert not bfs(a)[0] and not bfs(b)[0]
            assert bfs(a+(0,))[0] and not bfs(b+(0,))[0]
            return dict(checks=checks,left=a,right=b,suffix=[0],
                        meaning='Same counts, first/last color, run count and heavy-run count do not determine continuation behavior')
        assert str(status)=='unsat', 'A timeout is not an impossibility certificate'
    raise AssertionError('No expected witness')


def binary_control():
    x=sp.symbols('x'); fib=x/(1-x-x*x)
    gf=sp.factor(1+1/(1-2*x)-1-2*x-2*x*x*(2*fib+x*sp.diff(fib,x))
                 -x*x/(1+x)-x*x/(1-x))
    # Exact polynomial division computes coefficients without floating point.
    numerator,denominator=sp.Poly(sp.numer(gf),x),sp.Poly(sp.denom(gf),x)
    coeff=[]
    for n in range(15):
        value=numerator.nth(n)-sum(denominator.nth(j)*coeff[n-j] for j in range(1,min(n,denominator.degree())+1))
        coeff.append(int(value/denominator.nth(0)))
    direct=[sum(bfs(w)[0] for w in product(range(2),repeat=n)) for n in range(15)]
    assert coeff==direct
    return dict(source='Burns–Purcell binary formula; not a newly discovered formula',
                generating_function=str(gf),denominator_degree=denominator.degree(),
                exact_coefficients=coeff,
                lesson='Growing word-Hankel rank does not exclude a rational length-counting generating function')


if __name__=='__main__':
    results=dict(sympy=sp.__version__,z3=get_version_string(),
        hankel=[hankel(q,d) for q in (2,3) for d in range(2,6)],
        collision=summary_collision(),binary_control=binary_control(),
        assurance='Exact computational certificates, not Lean-certified rank or synthesis theorems',
        novelty='No priority claim; finite rank does not establish infinite rank or solve ternary enumeration')
    (ROOT/'residual-results.json').write_text(json.dumps(results,indent=2)+'\n')
    print(json.dumps({**results,'hankel':[{k:v for k,v in row.items() if k!='minor_certificate'} for row in results['hankel']]},indent=2))
