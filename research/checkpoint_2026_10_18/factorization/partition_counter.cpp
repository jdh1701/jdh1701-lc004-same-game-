// Independent fixed-width join/compression engine. Witnesses supplied by Python.
// Supports n<=16. All signed additions are checked for overflow.
#include <algorithm>
#include <cstdint>
#include <iostream>
#include <limits>
#include <stdexcept>
#include <unordered_map>

using Key=std::uint64_t;
using Coeff=std::int64_t;
using Map=std::unordered_map<Key,Coeff>;

void add(Map& m, Key k, Coeff v) {
  auto it=m.find(k);
  if(it==m.end()) { if(v) m.emplace(k,v); return; }
  Coeff out;
  if(__builtin_add_overflow(it->second,v,&out)) throw std::overflow_error("coefficient addition");
  if(out) it->second=out; else m.erase(it);
}

Key join(Key p,Key q,int n) {
  int parent[16], first[16], labels[16];
  for(int i=0;i<n;++i) parent[i]=i;
  auto root=[&](int i) {
    while(parent[i]!=i) {parent[i]=parent[parent[i]];i=parent[i];}
    return i;
  };
  for(Key w:{p,q}) {
    std::fill(first,first+16,-1);
    for(int i=0;i<n;++i) {
      int c=(w>>(4*i))&15;
      if(first[c]<0) first[c]=i;
      parent[root(i)]=root(first[c]);
    }
  }
  std::fill(labels,labels+16,-1);
  int next=0;
  Key out=0;
  for(int i=0;i<n;++i) {
    int r=root(i);
    if(labels[r]<0) labels[r]=next++;
    out|=Key(labels[r])<<(4*i);
  }
  return out;
}

int main() {
  int n;
  if(!(std::cin>>n)||n<0||n>16) return 2;
  Map coeff,delta;
  Key p;
  std::size_t witnesses=0,peak=0;
  while(std::cin>>p) {
    delta.clear();
    add(delta,p,1);
    for(auto [r,a]:coeff) {
      if(a==std::numeric_limits<Coeff>::min()) throw std::overflow_error("coefficient negation");
      add(delta,join(r,p,n),-a);
    }
    for(auto [r,a]:delta) add(coeff,r,a);
    peak=std::max(peak,coeff.size());
    ++witnesses;
  }
  std::cerr<<"{\"n\":"<<n<<",\"witnesses\":"<<witnesses
           <<",\"terms\":"<<coeff.size()<<",\"peak\":"<<peak<<"}\n";
  for(auto [p,a]:coeff) std::cout<<p<<' '<<a<<'\n';
}
