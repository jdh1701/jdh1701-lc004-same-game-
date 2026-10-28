from functools import lru_cache
from itertools import product

@lru_cache(None)
def win(w):
    if not w: return True
    i=0
    while i<len(w):
        j=i+1
        while j<len(w) and w[j]==w[i]: j+=1
        if j-i>=2 and win(w[:i]+w[j:]): return True
        i=j
    return False

def first_naive_failure(q,maxn):
    for n in range(maxn+1):
        for w in product(range(q),repeat=n):
            if not win(w): continue
            for i in range(n+1):
                for a in range(q):
                    z=w[:i]+(a,a)+w[i:]
                    l=i; r=i+2
                    while l>0 and z[l-1]==a: l-=1
                    while r<len(z) and z[r]==a: r+=1
                    rem=z[:l]+z[r:]
                    if not win(rem):
                        return {"q":q,"original":w,"gap":i,"inserted":z,
                                "delete_inserted_maximal_run_leaves":rem,
                                "inserted_word_wins":win(z)}
    return None

if __name__ == "__main__":
    print(first_naive_failure(2,10))
    assert win((0,1,1,0))
    assert win((0,0,0,1,1,0))
    assert not win((1,1,0))
