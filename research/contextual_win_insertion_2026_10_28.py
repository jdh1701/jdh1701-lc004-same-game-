from functools import lru_cache
from itertools import product

@lru_cache(None)
def winning(word):
    if not word:
        return True
    i = 0
    while i < len(word):
        j = i + 1
        while j < len(word) and word[j] == word[i]:
            j += 1
        if j - i >= 2 and winning(word[:i] + word[j:]):
            return True
        i = j
    return False

def check(q, max_original_length):
    words = [
        w for n in range(max_original_length + 1)
        for w in product(range(q), repeat=n) if winning(w)
    ]
    tests = 0
    for outer in words:
        for inner in words:
            for gap in range(len(outer) + 1):
                candidate = outer[:gap] + inner + outer[gap:]
                tests += 1
                if not winning(candidate):
                    print("COUNTEREXAMPLE", q, outer, inner, gap, candidate)
                    raise AssertionError("Winning-language insertion closure failed")
    print(q, max_original_length, len(words), tests, "PASS", flush=True)

if __name__ == "__main__":
    for params in [(2,8),(3,7),(4,6)]:
        check(*params)
