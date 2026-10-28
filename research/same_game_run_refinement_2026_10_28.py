from itertools import product

def parts(n):
    if n<2: raise ValueError(n)
    return [2]*(n//2) if n%2==0 else [3]+[2]*((n-3)//2)

def maximal_steps(w):
    i=0
    while i<len(w):
        j=i+1
        while j<len(w) and w[j]==w[i]:j+=1
        if j-i>=2: yield i,j,w[:i]+w[j:]
        i=j

def refine_step(w,i,j):
    s=w
    for k in parts(j-i):
        assert s[i:i+k]==(w[i],)*k
        s=s[:i]+s[i+k:]
    return s

total=0
for q,N in [(2,12),(3,10),(4,8)]:
    checks=0
    for n in range(N+1):
        for w in product(range(q),repeat=n):
            for i,j,target in maximal_steps(w):
                assert refine_step(w,i,j)==target
                checks+=1
    total+=checks
    print(q,N,checks,flush=True)
print('total',total)
