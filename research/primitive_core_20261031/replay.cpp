// Regenerate the COMPLETE original 2/3 family; no SCC test is used here.
#include <algorithm>
#include <array>
#include <cassert>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <sstream>
#include <string>
#include <vector>
using Block=std::vector<int>;
using Option=std::array<Block,2>;
std::vector<Option> local;
std::array<std::array<unsigned,5>,1024> table;
bool crossing(const Block&a,const Block&b) {
  for(unsigned i=0;i<a.size();++i)for(unsigned j=i+1;j<a.size();++j) {
    int lo=std::min(a[i],a[j]),hi=std::max(a[i],a[j]),inside=0;
    for(int x:b)inside+=(lo<x&&x<hi);
    if(inside>0&&inside<(int)b.size())return true;
  }
  return false;
}
void prepare() {
  for(int a=0;a<5;++a)for(int b=a+1;b<5;++b) {
    Option o;o[0]={a,b};for(int i=0;i<5;++i)if(i!=a&&i!=b)o[1].push_back(i);
    if(!crossing(o[0],o[1]))local.push_back(o);
  }
  assert(local.size()==5);
  for(unsigned mask=0;mask<1024;++mask)if(__builtin_popcount(mask)==5) {
    Block gs[2];for(int i=0;i<10;++i)gs[(mask>>i&1)?0:1].push_back(i);
    Option placed[2][5];
    for(int c=0;c<2;++c)for(int s=0;s<5;++s)for(int b=0;b<2;++b)
      for(int x:local[s][b])placed[c][s][b].push_back(gs[c][x]);
    for(int s=0;s<5;++s)for(int t=0;t<5;++t) {
      bool ok=true;for(const auto&a:placed[0][s])for(const auto&b:placed[1][t])if(crossing(a,b))ok=false;
      if(ok)table[mask][s]|=1u<<t;
    }
  }
}
int main(int argc,char**argv) {
  if(argc!=3)return 2;
  int j=std::stoi(argv[1]);if(j<2||j>12)return 2;
  prepare();std::ifstream in(argv[2]);if(!in)return 2;
  std::string line;std::uint64_t rows=0,nodes=0;
  while(std::getline(in,line)) {
    std::istringstream row(line);int n=3*j;
    std::vector<std::array<int,6>> ss(j);std::vector<int> core(n,-1),ones(n,0);
    for(int a=0;a<j;++a) {
      for(int&v:ss[a]){row>>v;assert(row&&v>=0&&v<n);}
      assert(ss[a][0]<ss[a][1]&&ss[a][1]<ss[a][2]);
      for(int k=0;k<3;++k){assert(core[ss[a][k]]==-1);core[ss[a][k]]=a;}
      auto copy=std::array<int,3>{ss[a][3],ss[a][4],ss[a][5]};std::sort(copy.begin(),copy.end());
      for(int k=0;k<3;++k)assert(copy[k]==ss[a][k]);
      ones[ss[a][3]]=1;
    }
    int trailing;assert(!(row>>trailing));
    std::vector<Block> gs(j);std::vector<int> start(n);
    int pos=0;
    for(int i=0;i<n;++i) {
      assert(core[i]>=0&&core[i]!=core[(i+1)%n]);start[i]=pos;
      for(int k=0;k<(ones[i]?1:2);++k)gs[core[i]].push_back(pos++);
    }
    assert(pos==5*j);
    std::vector<std::vector<std::array<unsigned,5>>> rel(j,std::vector<std::array<unsigned,5>>(j));
    std::vector<unsigned> connected(j);
    for(int a=0;a<j;++a) {
      connected[a]=1u<<a;assert(gs[a].size()==5);
      for(int b=0;b<a;++b) {
        unsigned mask=0;int ia=0,ib=0;
        for(int k=0;k<10;++k) {
          if(ia<5&&(ib==5||gs[a][ia]<gs[b][ib])){mask|=1u<<k;++ia;}else ++ib;
        }
        rel[a][b]=table[mask];
        for(int s=0;s<5;++s)for(int t=0;t<5;++t)if(table[mask][s]>>t&1)rel[b][a][t]|=1u<<s;
        if(crossing(gs[a],gs[b])){connected[a]|=1u<<b;connected[b]|=1u<<a;}
      }
    }
    for(int k=0;k<j;++k)for(int a=0;a<j;++a)if(connected[a]>>k&1)connected[a]|=connected[k];
    assert(connected[0]==(1u<<j)-1);
    std::vector<int> expected[2];expected[0].resize(j);expected[1].resize(j);
    for(int a=0;a<j;++a)for(int h=0;h<2;++h) {
      int at=start[ss[a][h?4:5]],found=-1;
      for(int s=0;s<5;++s)if(gs[a][local[s][0][0]]==at&&gs[a][local[s][0][1]]==at+1)found=s;
      assert(found>=0);expected[h][a]=found;
    }
    std::vector<int> assignment(j,-1);int solutions=0;bool seen[2]={false,false};
    auto solve=[&](auto&&self,int depth)->void {
      ++nodes;
      if(depth==j) {
        ++solutions;
        for(int h=0;h<2;++h)if(assignment==expected[h])seen[h]=true;
        if(solutions>2){std::cerr<<"THIRD CERTIFICATE row "<<rows+1<<'\n';std::exit(3);}
        return;
      }
      int best=-1,bestsize=6;unsigned domain=0;
      for(int a=0;a<j;++a)if(assignment[a]<0) {
        unsigned d=31;
        for(int b=0;b<j;++b)if(assignment[b]>=0)d&=rel[b][a][assignment[b]];
        int size=__builtin_popcount(d);if(!size)return;
        if(size<bestsize){best=a;bestsize=size;domain=d;}
      }
      for(int s=0;s<5;++s)if(domain>>s&1){assignment[best]=s;self(self,depth+1);assignment[best]=-1;}
    };
    solve(solve,0);assert(solutions==2&&seen[0]&&seen[1]);
    // Independent local joins of the two actual 2/3 partitions are full.
    for(int a=0;a<j;++a) {
      int parent[5]={0,1,2,3,4};auto find=[&](int x){while(parent[x]!=x)x=parent[x];return x;};
      for(int h=0;h<2;++h)for(const auto&b:local[expected[h][a]])for(int x:b)parent[find(x)]=find(b[0]);
      for(int x=0;x<5;++x)assert(find(x)==find(0));
    }
    ++rows;
  }
  std::cout<<"{\"classes\":"<<j<<",\"complete_original_family_replays\":"<<rows<<",\"csp_nodes\":"<<nodes<<",\"failures\":0}\n";
}
