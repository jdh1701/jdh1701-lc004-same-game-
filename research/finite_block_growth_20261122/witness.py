"""Exact capped-stack subset automaton. Count inputs, including each input only once."""
from itertools import product

def automaton(cap):
    stacks = [()]
    for s in stacks:
        if len(s)<cap:
            stacks.extend((a,)+s for a in range(3) if not s or a!=s[0])
    ids={s:i for i,s in enumerate(stacks)}
    moves=[]
    for s in stacks:
        row=[]
        for a in range(3):
            if s and s[0]==a: v=(1<<ids[s]) | (1<<ids[s[1:]])
            elif len(s)<cap: v=1<<ids[(a,)+s]
            else: v=0
            row.append(v)
        moves.append(row)
    states=[1]; index={1:0}; rows=[]
    for st in states:
        targets=[0,0,0]; v=st
        while v:
            i=(v&-v).bit_length()-1
            v &= v-1
            for a in range(3): targets[a] |= moves[i][a]
        row=[]
        for t in targets:
            if t not in index: index[t]=len(states); states.append(t)
            row.append(index[t])
        rows.append(row)
    return states,rows

def search(cap,limit):
    states,rows=automaton(cap)
    print('cap',cap,'states',len(states),flush=True)
    active=[0]*len(states); active[0]=1
    total=1; best=(0,1,0)
    for n in range(1,limit+1):
        nxt=[0]*len(states)
        for count,(i,j,k) in zip(active,rows):
            nxt[i]+=count; nxt[j]+=count; nxt[k]+=count
        active=nxt; total*=3
        assert sum(active)==total
        wins=sum(c for c,s in zip(active,states) if s&1)
        if wins:
            d=max(2,((total-1)//wins).bit_length())
            if n*best[1]>best[0]*d:
                best=(n,d,wins)
    n,d,wins=best
    print('best n,d',n,d,'wins',wins,flush=True)
    return best
def direct(word, cap):
    if not word:
        return True
    def visit(stack, i):
        if i == len(word):
            return not stack
        a = word[i]
        if stack and stack[-1] == a:
            return visit(stack[:-1], i+1) or visit(stack, i+1)
        return len(stack) < cap and visit(stack+(a,), i+1)
    return visit((),0)

def check_small(cap):
    states,rows = automaton(cap)
    for word in product(range(3),repeat=6):
        state=0
        for a in word:
            state=rows[state][a]
        assert bool(states[state]&1) == direct(word,cap)

if __name__=='__main__':
    for cap in (1,2,3,4):
        check_small(cap)
        search(cap,320)
