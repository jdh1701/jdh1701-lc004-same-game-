"""Independent exhaustive original maximal-run Same Game solver versus
direct deterministic CFG recognition/counting. No grammar equivalence assumed.
"""
from direct_grammar_dfa import compute
from functools import lru_cache
from itertools import product

@lru_cache(None)
def maximal_win(word):
    if not word:return True
    i=0
    while i<len(word):
        j=i+1
        while j<len(word) and word[i]==word[j]:j+=1
        if j-i>=2 and maximal_win(word[:i]+word[j:]):return True
        i=j
    return False

for q, lengths in [(2,range(11)),(3,range(11)),(4,range(9))]:
    for n in lengths:
        grammar_count,levels,edges,closed=compute(q,n)
        game_count=sum(maximal_win(w) for w in product(range(q),repeat=n))
        assert grammar_count==game_count, (q,n,grammar_count,game_count)
        print('PASS',q,n,grammar_count,'max_states',max(levels),flush=True)
print('ALL COMPARISONS PASSED')
