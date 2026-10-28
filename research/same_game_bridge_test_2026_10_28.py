from functools import lru_cache
from itertools import product
import json

@lru_cache(None)
def win(w):
    if not w:
        return True
    i = 0
    while i < len(w):
        j = i + 1
        while j < len(w) and w[j] == w[i]:
            j += 1
        if j - i >= 2 and win(w[:i] + w[j:]):
            return True
        i = j
    return False

def check(q, max_n):
    tested = 0
    for n in range(2, max_n + 1):
        for w in product(range(q), repeat=n):
            if win(w):
                continue
            for i in range(n-1):
                if w[i] != w[i+1]:
                    continue
                for size in (2, 3):
                    if i + size > n or any(w[j] != w[i] for j in range(i, i+size)):
                        continue
                    v = w[:i] + w[i+size:]
                    tested += 1
                    if win(v):
                        return {"q":q,"n":n,"tested":tested,"counterexample":w,"remainder":v,"index":i,"deleted":size}
    return {"q":q,"max_n":max_n,"tested":tested,"counterexample":None}

if __name__ == "__main__":
    print(json.dumps([check(2,12),check(3,12),check(4,9)], indent=2))
