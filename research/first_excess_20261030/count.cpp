// Exhaustive original-position (5,5,6) census; no assumed coefficient signs.
#include <array>
#include <vector>
#include <map>
#include <fstream>
#include <iostream>
#include <cassert>
#include <cstdint>
#include <algorithm>
using U=uint32_t;using I=int64_t;
struct Rel{uint64_t allowed;bool cross;};
std::array<Rel,1024> t55;std::array<Rel,2048> t56;
int S,top6;std::vector<std::array<int,8>> jt;
int compress(U a,U b){U u=a|b;int out=0,i=0;while(u){U bit=u&-u;if(a&bit)out|=1<<i;++i;u-=bit;}return out;}
bool crosses(U a,U b){U u=a|b;int last=-1,runs=0;while(u){U bit=u&-u;int c=bool(a&bit);runs+=c!=last;last=c;u-=bit;}return runs>=4;}
bool connected(U a,U b,U c){std::vector<U> v={a,b,c};for(;;){bool merged=false;for(size_t i=0;i<v.size()&&!merged;++i)for(size_t j=0;j<i;++j)if(crosses(v[i],v[j])){v[j]|=v[i];v.erase(v.begin()+i);merged=true;break;}if(!merged)return v.size()==1;}}
int j5(int a,int b){return a==0?b:(a==b?a:6);}
I coefficient(const std::vector<std::array<int,3>>& cs){
 std::vector<I> dp(49*S),next;dp[0]=1;
 for(auto c:cs){next=dp;for(int a=0;a<7;++a)for(int b=0;b<7;++b)for(int z=0;z<S;++z){I v=dp[(a*7+b)*S+z];if(!v)continue;int dst=(j5(a,c[0]+1)*7+j5(b,c[1]+1))*S+jt[z][c[2]];next[dst]-=v;assert(next[dst]>-(I(1)<<50)&&next[dst]<(I(1)<<50));}dp.swap(next);}
 return -dp[(6*7+6)*S+top6];
}
int main(int argc,char**argv){
 assert(argc==3);std::ifstream in(argv[1]);assert(in);in>>S>>top6;jt.resize(S);for(auto&r:jt)for(int&v:r)in>>v;
 for(auto&r:t55)in>>r.allowed>>r.cross;
 for(auto&r:t56)in>>r.allowed>>r.cross;
 assert(in);
 std::ofstream out(argv[2]);assert(out);std::map<I,I> hist;std::map<int,I> genhist;I total=0,nc=0,withgen=0,full=0,sum=0,nonzero=0;U all=(1<<16)-1;
 for(U c=0;c<=all;++c)if(__builtin_popcount(c)==6){
  U rem=all^c;std::vector<int> v;for(int i=0;i<16;++i)if(rem>>i&1)v.push_back(i);
  for(int i=1;i<7;++i)for(int j=i+1;j<8;++j)for(int k=j+1;k<9;++k)for(int l=k+1;l<10;++l){
   U a=(1<<v[0])|(1<<v[i])|(1<<v[j])|(1<<v[k])|(1<<v[l]),b=rem^a;++total;
   if(!connected(a,b,c))continue;
   ++nc;
   auto ab=t55[compress(a,b)];auto ac=t56[compress(a,c)];auto bc=t56[compress(b,c)];
   std::vector<std::array<int,3>> cs;U xa=0,xb=0;int zjoin=0;
   if(ab.allowed&&ac.allowed&&bc.allowed)for(int x=0;x<5;++x)for(int y=0;y<5;++y)if(ab.allowed>>(5*x+y)&1)for(int z=0;z<8;++z)if((ac.allowed>>(8*x+z)&1)&&(bc.allowed>>(8*y+z)&1)){cs.push_back({x,y,z});xa|=1<<x;xb|=1<<y;zjoin=jt[zjoin][z];}
   if(!cs.empty())++withgen;
   I val=0;
   if(__builtin_popcount(xa)>=2&&__builtin_popcount(xb)>=2&&zjoin==top6){++full;val=coefficient(cs);}
   ++hist[val];sum+=val;
   if(val){++nonzero;++genhist[cs.size()];out<<a<<' '<<b<<' '<<c<<' '<<val<<' '<<cs.size()<<'\n';}
  }
 }
 assert(total==1009008);
 std::cout<<"{\"status\":\"VERIFIED-COMP\",\"profile\":[5,5,6],\"patterns\":"<<total<<",\"nc_connected\":"<<nc<<",\"with_generators\":"<<withgen<<",\"full_join\":"<<full<<",\"nonzero\":"<<nonzero<<",\"coefficient_sum\":"<<sum<<",\"histogram\":{";
 bool first=true;for(auto [x,n]:hist){if(!first)std::cout<<',';first=false;std::cout<<'"'<<x<<"\":"<<n;}std::cout<<"},\"nonzero_generator_histogram\":{";first=true;for(auto[x,n]:genhist){if(!first)std::cout<<',';first=false;std::cout<<'"'<<x<<"\":"<<n;}std::cout<<"}}\n";
}
