// Count NC-connected all-five patterns x on n=5j points with their signed join coefficient c(x).
// usage: five_kernel n shards shard   (sharding by index of candidate at depth 8)
#include <bits/stdc++.h>
using namespace std;
int n, J, T, R; int lab[40]; int cnt[8]; long long pref = 0;
map<int,long long> dist; long long candidates = 0, withAtoms = 0;
vector<array<signed char,40>> atoms; // block labels
vector<int> pos[8];

static bool crossing_pair(const vector<int>& A, const vector<int>& B) {
  // restricted word of A and B contains a b a b ? (positions sorted)
  vector<pair<int,int>> w; for (int p: A) w.push_back({p,0}); for (int p: B) w.push_back({p,1});
  sort(w.begin(), w.end());
  int state = 0; int first = w[0].second; // look for subsequence first,other,first,other
  int pat[4] = {first, 1-first, first, 1-first};
  for (auto& e: w) if (e.second == pat[state]) { if (++state == 4) return true; }
  return false;
}
static bool nc_blocks(const vector<int>& A, const vector<int>& B) { return !crossing_pair(A, B); }

bool connected() {
  // closure: merge groups of classes that cross (as unions of positions), repeat
  vector<vector<int>> g(J); for (int c = 0; c < J; c++) g[c] = pos[c];
  bool ch = true;
  while (ch && g.size() > 1) {
    ch = false;
    for (size_t a = 0; a < g.size() && !ch; a++) for (size_t b = a + 1; b < g.size() && !ch; b++)
      if (crossing_pair(g[a], g[b])) { g[a].insert(g[a].end(), g[b].begin(), g[b].end()); g.erase(g.begin() + b); ch = true; }
  }
  return g.size() == 1;
}

vector<vector<int>> blocks; // current chosen blocks
void atom_rec(int c) {
  if (c == J) {
    array<signed char,40> a; a.fill(-1); int b = 0;
    for (auto& blk: blocks) { for (int p: blk) a[p] = b; b++; }
    atoms.push_back(a); return;
  }
  const auto& P = pos[c];
  for (int i = 0; i < 5; i++) for (int k = i + 1; k < 5; k++) {
    vector<int> pr = {P[i], P[k]}, tr;
    for (int t = 0; t < 5; t++) if (t != i && t != k) tr.push_back(P[t]);
    if (!nc_blocks(pr, tr)) continue;
    bool ok = true;
    for (auto& blk: blocks) if (!nc_blocks(blk, pr) || !nc_blocks(blk, tr)) { ok = false; break; }
    if (!ok) continue;
    blocks.push_back(pr); blocks.push_back(tr);
    atom_rec(c + 1);
    blocks.pop_back(); blocks.pop_back();
  }
}

typedef array<signed char,40> Part;
Part canon(const int* l) { Part r; r.fill(-1); int m[64]; memset(m, -1, sizeof m); int nx = 0; for (int i = 0; i < n; i++) { if (m[l[i]] < 0) m[l[i]] = nx++; r[i] = m[l[i]]; } return r; }
Part joinp(const Part& x, const Part& y) {
  int par[40]; for (int i = 0; i < n; i++) par[i] = i;
  function<int(int)> f = [&](int a) { while (par[a] != a) { par[a] = par[par[a]]; a = par[a]; } return a; };
  for (const Part* z: {&x, &y}) { int first[40]; memset(first, -1, sizeof first);
    for (int i = 0; i < n; i++) { int v = (*z)[i]; if (first[v] >= 0) { int a = f(first[v]), b = f(i); if (a != b) par[b] = a; } else first[v] = i; } }
  int l[40]; for (int i = 0; i < n; i++) l[i] = f(i); return canon(l);
}
long long coefficient(const Part& target) {
  map<Part,long long> coef;
  for (auto& g0: atoms) { int l[40]; for (int i = 0; i < n; i++) l[i] = g0[i]; Part g = canon(l);
    map<Part,long long> add; for (auto& kv: coef) { Part z = joinp(kv.first, g); add[z] -= kv.second; }
    add[g] += 1;
    for (auto& kv: add) { coef[kv.first] += kv.second; }
    for (auto it = coef.begin(); it != coef.end();) it = (it->second == 0) ? coef.erase(it) : next(it);
  }
  auto it = coef.find(target); return it == coef.end() ? 0 : it->second;
}
vector<Part> found;
void process() {
  candidates++;
  for (int c = 0; c < J; c++) pos[c].clear();
  for (int i = 0; i < n; i++) pos[lab[i]].push_back(i);
  if (!connected()) return;
  atoms.clear(); blocks.clear(); atom_rec(0);
  if (atoms.empty()) { dist[0]++; return; }
  withAtoms++;
  int l[40]; for (int i = 0; i < n; i++) l[i] = lab[i]; Part tg = canon(l);
  long long c = coefficient(tg); dist[(int)c]++; if (c) found.push_back(tg);
}
void rec(int i, int used) {
  if (i == n) { process(); return; }
  if (i == 8) { if ((pref++) % T != R) return; }
  for (int c = 0; c < min(used + 1, J); c++) if (cnt[c] < 5) { lab[i] = c; cnt[c]++; rec(i + 1, max(used, c + 1)); cnt[c]--; }
}
int main(int argc, char** argv) {
  n = atoi(argv[1]); J = n / 5; T = atoi(argv[2]); R = atoi(argv[3]);
  rec(0, 0);
  printf("n=%d shard %d/%d candidates=%lld withAtoms=%lld dist:", n, R, T, candidates, withAtoms);
  for (auto& kv: dist) printf(" [%d]=%lld", kv.first, kv.second);
  printf("\n");
  for (auto& p: found) { for (int i = 0; i < n; i++) putchar('a' + p[i]); putchar('\n'); }
}
