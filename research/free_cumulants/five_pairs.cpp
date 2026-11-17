// Count kernel candidates via certificate pairs: x = a join b with exactly two certificates (atoms) below x,
// x all-five and NC-connected. Enumerate (a, matching of pairs to triples of a) -> x, test atoms==2, count x once (a = min atom).
// usage: five_pairs n shards shard
#include <bits/stdc++.h>
using namespace std;
int n, J, T, R; long long aidx = 0;
typedef array<signed char,40> Part;
vector<vector<int>> cur; // blocks of current certificate
int pairsLeft, triplesLeft;
long long cnt = 0, xs = 0, connectedXs = 0;
static bool cross(const vector<int>& A0, const vector<int>& B0) {
  // blocks may be unsorted for pair/triple built from sorted classes; sort small copies on stack
  int a[40], b[40]; int na=A0.size(), nb=B0.size();
  for(int i=0;i<na;i++)a[i]=A0[i]; for(int i=0;i<nb;i++)b[i]=B0[i];
  sort(a,a+na); sort(b,b+nb);
  int i=0,j=0,st=0,f=-1,last=-1; // merge, track alternation a b a b of runs
  int runs=0; int prev=-1;
  while(i<na||j<nb){ int who; if(j>=nb||(i<na&&a[i]<b[j])){who=0;i++;} else {who=1;j++;}
    if(who!=prev){runs++;prev=who; if(runs>=4) return true;} }
  return false; }
Part canonl(const int* l) { Part r; r.fill(-1); int m[64]; memset(m,-1,sizeof m); int nx=0; for (int i=0;i<n;i++){ if(m[l[i]]<0) m[l[i]]=nx++; r[i]=m[l[i]]; } return r; }
Part joinp(const Part& x, const Part& y) { int par[40]; for(int i=0;i<n;i++)par[i]=i;
  function<int(int)> f=[&](int a){ while(par[a]!=a){par[a]=par[par[a]];a=par[a];} return a;};
  for (const Part* z: {&x,&y}) { int first[40]; memset(first,-1,sizeof first);
    for(int i=0;i<n;i++){int v=(*z)[i]; if(first[v]>=0){int a=f(first[v]),b=f(i); if(a!=b)par[b]=a;} else first[v]=i;} }
  int l[40]; for(int i=0;i<n;i++) l[i]=f(i); return canonl(l); }
bool connectedClasses(vector<vector<int>> g) {
  bool ch = true; while (ch && g.size() > 1) { ch = false;
    for (size_t a=0;a<g.size()&&!ch;a++) for(size_t b=a+1;b<g.size()&&!ch;b++) if (cross(g[a],g[b])) { g[a].insert(g[a].end(),g[b].begin(),g[b].end()); g.erase(g.begin()+b); ch=true; } }
  return g.size()==1; }
// atoms below x (all classes size 5): enumerate splits into pair+triple, NC; abort after limit
vector<vector<int>> cls; vector<vector<int>> blk; vector<Part> found; int limitAtoms;
bool ncAll(const vector<int>& pr, const vector<int>& tr) {
  if (cross(pr,tr)) return false; for (auto& b: blk) if (cross(b,pr)||cross(b,tr)) return false; return true; }
void atomRec(int c) {
  if ((int)found.size() > limitAtoms) return;
  if (c == (int)cls.size()) { int l[40]; for (size_t b=0;b<blk.size();b++) for (int p: blk[b]) l[p]=b; found.push_back(canonl(l)); return; }
  const auto& P = cls[c];
  for (int i=0;i<5;i++) for (int k=i+1;k<5;k++) { vector<int> pr={P[i],P[k]},tr; for(int t=0;t<5;t++) if(t!=i&&t!=k) tr.push_back(P[t]);
    if(!ncAll(pr,tr)) continue; blk.push_back(pr); blk.push_back(tr); atomRec(c+1); blk.pop_back(); blk.pop_back();
    if ((int)found.size() > limitAtoms) return; } }
void testCertificate() {
  // cur = blocks of a. pairs and triples
  vector<int> prs, trs; for (size_t i=0;i<cur.size();i++) (cur[i].size()==2?prs:trs).push_back(i);
  if ((int)prs.size()!=J || (int)trs.size()!=J) return;
  if ((aidx++) % T != R) return;
  int l[40]; for (size_t b=0;b<cur.size();b++) for(int p: cur[b]) l[p]=b; Part a = canonl(l);
  vector<int> perm(J); iota(perm.begin(), perm.end(), 0);
  do {
    vector<vector<int>> g; for (int i=0;i<J;i++){ vector<int> u=cur[prs[i]]; for(int p: cur[trs[perm[i]]]) u.push_back(p); sort(u.begin(),u.end()); g.push_back(u);} 
    xs++;
    if (!connectedClasses(g)) continue; connectedXs++;
    cls = g; blk.clear(); found.clear(); limitAtoms = 2; atomRec(0);
    if (found.size() != 2) continue;
    int lx[40]; for (int i=0;i<J;i++) for(int p: g[i]) lx[p]=i; Part x = canonl(lx);
    if (joinp(found[0], found[1]) != x) continue;
    // count x once: a must be the lexicographically smaller of the two atoms
    if (!(found[0] == a || found[1] == a)) continue;
    Part other = (found[0]==a) ? found[1] : found[0];
    if (a < other) cnt++;
  } while (next_permutation(perm.begin(), perm.end()));
}
vector<char> used;
void gen(int pos, int pl, int tl) {
  while (pos < n && used[pos]) pos++;
  if (pos == n) { testCertificate(); return; }
  used[pos] = 1;
  for (int sz=2; sz<=3; sz++) {
    if (sz==2 && pl==0) continue; if (sz==3 && tl==0) continue;
    // choose sz-1 further positions among unused > pos
    vector<int> cand; for (int p=pos+1;p<n;p++) if(!used[p]) cand.push_back(p);
    vector<int> idx(sz-1);
    function<void(int,int)> pick=[&](int k,int start){
      if (k==sz-1){ vector<int> b={pos}; for(int v:idx) b.push_back(cand[v]);
        for(auto& o:cur) if(cross(o,b)) return;
        for(int p: b) used[p]=1; cur.push_back(b); gen(pos+1, pl-(sz==2), tl-(sz==3)); cur.pop_back(); for(int p: b) used[p]=0; used[pos]=1; return; }
      for(int v=start; v<(int)cand.size(); v++){ idx[k]=v; pick(k+1,v+1);} };
    pick(0,0);
  }
  used[pos] = 0;
}
int main(int argc,char**argv){ n=atoi(argv[1]); J=n/5; T=atoi(argv[2]); R=atoi(argv[3]); used.assign(n,0); gen(0,J,J);
  printf("n=%d shard %d/%d certificates_sharded x_generated=%lld connected=%lld KERNEL_COUNT=%lld\n",n,R,T,xs,connectedXs,cnt); }
