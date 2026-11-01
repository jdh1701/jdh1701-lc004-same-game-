// Exact ternary support-state counting. No game solver and no word enumeration.
// Color permutations AND reversal of every stack are identified.
// Reversal preserves aggregated continuation counts, not labeled transitions.
#include <algorithm>
#include <array>
#include <cstdint>
#include <iostream>
#include <limits>
#include <stdexcept>
#include <unordered_map>
#include <vector>
using U=std::uint64_t;
using State=std::vector<U>;
struct Hash {
  size_t operator()(State const& s) const {
    U h=0x9e3779b97f4a7c15ULL;
    for (U x:s) {
      x=(x^(x>>30))*0xbf58476d1ce4e5b9ULL;
      x=(x^(x>>27))*0x94d049bb133111ebULL;
      h^=(x^(x>>31))+0x9e3779b97f4a7c15ULL+(h<<6)+(h>>2);
    }
    return h;
  }
};
const std::array<std::array<int,3>,6> perms={{{1,2,3},{1,3,2},{2,1,3},{2,3,1},{3,1,2},{3,2,1}}};
U rename(U w,std::array<int,3> const& p) {
  unsigned bit=63-__builtin_clzll(w);
  U root=U(1)<<bit, x=w^root, mask=0x5555555555555555ULL;
  U lo=x&mask,hi=(x>>1)&mask;
  U digit[3]={lo&~hi,hi&~lo,lo&hi};
  U out=root;
  for(int i=0;i<3;++i) {
    if(p[i]&1)out|=digit[i];
    if(p[i]&2)out|=digit[i]<<1;
  }
  return out;
}
U reverse_stack(U w) {
  U v=1;
  while(w!=1){v=(v<<2)|(w&3);w>>=2;}
  return v;
}
State canonical(State const& in) {
  State best=in;
  for(int rev=0;rev<2;++rev)for(int k=0;k<6;++k) {
    State s;s.reserve(in.size());
    for(U w:in)s.push_back(rename(rev?reverse_stack(w):w,perms[k]));
    std::sort(s.begin(),s.end());if(s<best)best=std::move(s);
  }
  return best;
}

State step(State const& s,int a,int remain) {
  State out;out.reserve(2*s.size());
  U cutoff=U(1)<<(2*std::min(remain,30)+1);
  for(U w:s) {
    if(w!=1 && (w&3)==U(a)) {
      if(w<cutoff)out.push_back(w);
      if((w>>2)<cutoff)out.push_back(w>>2);
    } else {
      U v=(w<<2)|U(a);
      if(v<cutoff)out.push_back(v);
    }
  }
  std::sort(out.begin(),out.end());
  out.erase(std::unique(out.begin(),out.end()),out.end());
  return canonical(out);
}
int main(int argc,char** argv) {
  int n=argc>1?std::stoi(argv[1]):18;
  size_t cap=argc>2?std::stoull(argv[2]):2000000;
  if(n<0 || n>40)throw std::runtime_error("n must be in 0..40 (checked uint64 range)");
  std::unordered_map<State,U,Hash> cur,nxt;
  cur[State{1}]=1;std::vector<size_t> levels{1};
  U edges=0;
  for(int i=0;i<n;++i) {
    nxt.clear();nxt.reserve(std::min(cap+1,cur.size()*3));
    std::vector<std::pair<State const*,U>> order;
    for(auto const& item:cur)order.push_back({&item.first,item.second});
    std::sort(order.begin(),order.end(),[](auto const& x,auto const& y){
      if(x.second!=y.second)return x.second>y.second;
      return *x.first<*y.first;
    });
    for(auto const& item:order){
      State dual;for(U w:*item.first)dual.push_back(reverse_stack(w));
      std::sort(dual.begin(),dual.end());
      std::array<State,3> children[2];
      std::pair<size_t,size_t> score[2];
      for(int rev=0;rev<2;++rev){
        score[rev]={0,0};
        for(int a=1;a<=3;++a){
          auto& child=children[rev][a-1];child=step(rev?dual:*item.first,a,n-i-1);
          if(child.empty())continue;
          bool duplicate=false;for(int j=0;j<a-1;++j)if(child==children[rev][j])duplicate=true;
          if(!duplicate && nxt.find(child)==nxt.end())++score[rev].first;
          score[rev].second+=child.size();
        }
      }
      int selected=score[1]<score[0]?1:0;
      for(auto& ns:children[selected]){
        if(ns.empty())continue;
        auto& value=nxt[std::move(ns)];
        if(value>std::numeric_limits<U>::max()-item.second)throw std::runtime_error("overflow");
        value+=item.second;++edges;
        if(nxt.size()>cap){
          std::cout<<"{\"n\":"<<n<<",\"status\":\"state_cap\",\"partial_depth\":"<<i+1<<"}\n";return 2;
        }
      }
    }
    cur.swap(nxt);levels.push_back(cur.size());
    std::cerr<<"depth "<<i+1<<" states "<<cur.size()<<"\n";
  }
  U count=0;
  for(auto const& item:cur)if(std::binary_search(item.first.begin(),item.first.end(),U(1)))count+=item.second;
  std::cout<<"{\"n\":"<<n<<",\"status\":\"complete\",\"count\":"<<count<<",\"edges\":"<<edges<<",\"states\":[";
  for(size_t i=0;i<levels.size();++i)std::cout<<(i?",":"")<<levels[i];
  std::cout<<"]}\n";
}
