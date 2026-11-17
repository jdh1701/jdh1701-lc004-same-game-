// Exhaust all feasible (5,5,5) restrictions, append the unique six-class.
// No assumed sign, generator count, or run-shape restriction.
#include "../scc_transfer_20261029/common.hpp"
#include <map>
#include <algorithm>
using I=int64_t;
std::array<uint64_t,2048> t56;
int S,top6;std::vector<std::array<int,8>> jt;
int compress(U a,U b){U u=a|b;int out=0,i=0;while(u){U bit=u&-u;if(a&bit)out|=1<<i;++i;u-=bit;}return out;}
bool crosses(U a,U b){U u=a|b;int last=-1,runs=0;while(u){U bit=u&-u;int c=bool(a&bit);runs+=c!=last;last=c;u-=bit;}return runs>=4;}
bool connected(std::vector<U> v){for(;;){bool merged=false;for(size_t i=0;i<v.size()&&!merged;++i)for(size_t j=0;j<i;++j)if(crosses(v[i],v[j])){v[j]|=v[i];v.erase(v.begin()+i);merged=true;break;}if(!merged)return v.size()==1;}}
int j5(int a,int b){return a==0?b:(a==b?a:6);}
I coefficient(const std::vector<std::array<int,4>>& cs){
 std::vector<I> dp(343*S),next;dp[0]=1;
 for(auto c:cs){next=dp;for(int a=0;a<7;++a)for(int b=0;b<7;++b)for(int d=0;d<7;++d)for(int z=0;z<S;++z){I v=dp[((a*7+b)*7+d)*S+z];if(!v)continue;int dst=((j5(a,c[0]+1)*7+j5(b,c[1]+1))*7+j5(d,c[2]+1))*S+jt[z][c[3]];next[dst]-=v;assert(next[dst]>-(I(1)<<50)&&next[dst]<(I(1)<<50));}dp.swap(next);}
 return -dp[342*S+top6];
}
int main(int argc,char**argv){
 assert(argc==3);std::string dir=argv[1];std::ifstream in(argv[2]);assert(in);
 in>>S>>top6;jt.resize(S);for(auto&r:jt)for(int&v:r)in>>v;
 for(auto&r:table)in>>r.allowed>>r.cross;
 for(auto&r:t56){bool cross;in>>r>>cross;}assert(in);
 uint64_t alltemplates=0;auto templates=makeTemplates3(alltemplates);assert(alltemplates==126126&&templates.size()==13355);
 uint64_t incidences=0;for(auto&t:templates)incidences+=t.solutions.size();assert(incidences==60060);
 std::ifstream orbits(dir+"/six_orbits.txt");assert(orbits);std::ofstream out(dir+"/survivors.txt"),per(dir+"/orbit_results.txt"),fullout(dir+"/full_join.txt");assert(out&&per&&fullout);
 U six;int weight;I weights=0,checked=0,feasible=0,conn=0,full=0,total=0,sum=0,certificate_incidences=0;std::map<I,I> values;std::map<int,I> gens;
 std::array<U,32768> physical{};std::array<uint64_t,32768> rel{};
 while(orbits>>six>>weight){weights+=weight;std::array<int,15> complement{};int n=0;for(int i=0;i<21;++i)if(!(six>>i&1))complement[n++]=i;assert(n==15);
  for(U m=1;m<32768;++m){physical[m]=physical[m&(m-1)]|(U(1)<<complement[low(m)]);if(__builtin_popcount(m)==5)rel[m]=t56[compress(physical[m],six)];}
  I hits=0;
  for(auto&t:templates){++checked;auto r0=rel[t.masks[0]],r1=rel[t.masks[1]],r2=rel[t.masks[2]];if(!(r0&&r1&&r2))continue;
   std::vector<std::array<int,4>> cs;std::array<U,3> used{};int zjoin=0;
   for(auto&s:t.solutions){unsigned zs=((r0>>(8*s[0]))&(r1>>(8*s[1]))&(r2>>(8*s[2])))&255;
    while(zs){int z=__builtin_ctz(zs);zs&=zs-1;cs.push_back({s[0],s[1],s[2],z});for(int k=0;k<3;++k)used[k]|=1<<s[k];zjoin=jt[zjoin][z];}}
   if(cs.empty())continue;
   feasible+=weight;certificate_incidences+=weight*cs.size();U a=physical[t.masks[0]],b=physical[t.masks[1]],c=physical[t.masks[2]];
   if(!connected({a,b,c,six}))continue;
   conn+=weight;if(zjoin!=top6||__builtin_popcount(used[0])<2||__builtin_popcount(used[1])<2||__builtin_popcount(used[2])<2)continue;
   full+=weight;I v=coefficient(cs);++values[v];
   fullout<<a<<' '<<b<<' '<<c<<' '<<six<<' '<<weight<<' '<<v<<' '<<cs.size()<<'\n';
   if(!v)continue;
   ++hits;total+=weight;sum+=weight*v;gens[cs.size()]+=weight;
   out<<a<<' '<<b<<' '<<c<<' '<<six<<' '<<weight<<' '<<v<<' '<<cs.size()<<'\n';
  }
  per<<six<<' '<<weight<<' '<<hits<<'\n';
 }
 assert(weights==54264&&certificate_incidences==276746400);std::cout<<"{\"profile\":[5,5,5,6],\"all_patterns\":"<<weights*alltemplates<<",\"completion_cases\":"<<checked<<",\"certificate_incidences\":"<<certificate_incidences<<",\"feasible\":"<<feasible<<",\"connected_feasible\":"<<conn<<",\"connected_full_join\":"<<full<<",\"nonzero\":"<<total<<",\"coefficient_sum\":"<<sum<<",\"weighted_nonzero_generator_histogram\":{";
 bool first=true;for(auto[x,v]:gens){if(!first)std::cout<<',';first=false;std::cout<<'"'<<x<<"\":"<<v;}std::cout<<"},\"unweighted_full_join_coefficient_histogram\":{";first=true;for(auto[x,v]:values){if(!first)std::cout<<',';first=false;std::cout<<'"'<<x<<"\":"<<v;}std::cout<<"}}\n";
}
