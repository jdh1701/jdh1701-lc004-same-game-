// Independent meet-in-the-middle count, using explicit half-word enumeration.
// Top-FIRST strings; no horizon pruning and no encoded-stack dynamic program.
#include <algorithm>
#include <array>
#include <cstdint>
#include <iostream>
#include <string>
#include <unordered_map>
#include <vector>
using U=std::uint64_t;
using S=std::vector<std::string>;
struct SH {size_t operator()(S const& s)const {
  size_t h=0;for(auto const& x:s)h^=std::hash<std::string>{}(x)+0x9e3779b9+(h<<6)+(h>>2);return h;
}};
S advance(S const& s,char a) {
  S out;for(auto const& t:s) {
    if(!t.empty() && t.front()==a){out.push_back(t);out.push_back(t.substr(1));}
    else out.push_back(a+t);
  }
  std::sort(out.begin(),out.end());out.erase(std::unique(out.begin(),out.end()),out.end());return out;
}
S orbit(S const& s) {
  std::string p="012";S best=s;
  do {S t=s;for(auto& w:t)for(char& a:w)a=p[a-'0'];std::sort(t.begin(),t.end());best=std::min(best,t);}while(std::next_permutation(p.begin(),p.end()));
  return best;
}
struct Posting {std::vector<std::uint32_t> ids;std::vector<U> bits;};
std::unordered_map<std::string,Posting> posting;
std::unordered_map<S,U,SH> left;
std::uint32_t right_words=0;
bool same_length;
void enumerate(int remain,S const& s,bool right) {
  if(remain==0) {
    if(right){for(auto const& t:s)posting[t].ids.push_back(right_words);++right_words;}
    if(!right || same_length)++left[orbit(s)];
    return;
  }
  for(char a='0';a<='2';++a)enumerate(remain-1,advance(s,a),right);
}
int main(int argc,char** argv) {
  int n=argc>1?std::stoi(argv[1]):20;
  if(n<0 || n>28){std::cerr<<"n must be in 0..28\n";return 2;}
  int l=n/2,r=n-l;same_length=l==r;
  enumerate(r,S{""},true);
  if(!same_length)enumerate(l,S{""},false);
  size_t width=(right_words+63)/64,dense=0,total_ids=0;
  for(auto& kv:posting) {
    auto& p=kv.second;total_ids+=p.ids.size();
    if(p.ids.size()>=1024){p.bits.assign(width,0);for(auto id:p.ids)p.bits[id/64]|=U(1)<<(id%64);p.ids.clear();p.ids.shrink_to_fit();++dense;}
  }
  std::cerr<<"left supports "<<left.size()<<" right words "<<right_words<<" postings "<<total_ids<<" dense "<<dense<<" width "<<width<<"\n";
  std::vector<U> hit(width);U total=0;size_t done=0;
  for(auto const& kv:left) {
    std::fill(hit.begin(),hit.end(),0);
    for(auto const& s:kv.first) {
      auto it=posting.find(s);if(it==posting.end())continue;auto const& p=it->second;
      if(p.bits.empty())for(auto id:p.ids)hit[id/64]|=U(1)<<(id%64);
      else for(size_t j=0;j<width;++j)hit[j]|=p.bits[j];
    }
    U accepted=0;for(U x:hit)accepted+=__builtin_popcountll(x);
    total+=accepted*kv.second;
    if(++done%50000==0)std::cerr<<"queried "<<done<<"\n";
  }
  std::cout<<"{\"n\":"<<n<<",\"status\":\"complete\",\"count\":"<<total<<",\"left_support_orbits\":"<<left.size()
    <<",\"right_words\":"<<right_words<<",\"total_postings\":"<<total_ids<<",\"dense_postings\":"<<dense<<"}\n";
}
