"""Held-out recurrence falsification on OEIS A035617 (lengths 0..25).
A fitted recurrence is NOT a mathematical theorem about future terms.
Requires sympy. Train on first 18 entries, test on last 8.
"""
import sympy as sp
vals=[1,0,3,3,15,33,105,297,879,2631,7833,23697,71385,
      216765,657849,2003151,6103743,18624693,56870385,
      173760513,531128349,1623881889,4965695331,
      15185222199,46435889601,141985777503]
train=18
for order in range(1,10):
    A=sp.Matrix([[vals[n-j] for j in range(1,order+1)]
                 for n in range(order,train)])
    y=sp.Matrix(vals[order:train])
    sol=sp.linsolve((A,y))
    if sol==sp.EmptySet:
        print(order,"inconsistent on training data")
        continue
    c=tuple(next(iter(sol)))
    if any(x.free_symbols for x in c):
        print(order,"underdetermined")
        continue
    failures=[n for n in range(train,len(vals))
              if sum(c[j-1]*vals[n-j] for j in range(1,order+1))!=vals[n]]
    print(order,"fits training", "holdout failures:",failures)
