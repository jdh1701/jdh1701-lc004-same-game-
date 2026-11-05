#include "common.hpp"
int main(int argc,char**argv){
  assert(argc==2);std::string dir=argv[1];
  std::ifstream tin(dir+"/geometry5.txt");assert(tin.good());
  for(auto&r:table){int c;tin>>r.allowed>>c;r.cross=c;}assert(tin.good());
  auto started=std::chrono::steady_clock::now();
  uint64_t templates_all=0;auto templates=makeTemplates3(templates_all);
  assert(templates_all==126126);
  std::ifstream oin(dir+"/first_block_orbits_20.txt");assert(oin.good());
  U first;int weight;uint64_t weighted_survivors=0,weighted_candidates=0,checked=0,orbits=0,weights=0;
  std::array<U,32768> physical;std::array<Rel,32768> rootRel;
  std::ofstream per(dir+"/orbit_results.txt");
  while(oin>>first>>weight){
    ++orbits;weights+=weight;
    std::array<int,15> complement{};int n=0;for(int i=0;i<20;++i)if(!((first>>i)&1))complement[n++]=i;
    assert(n==15);physical[0]=0;
    for(U m=1;m<32768;++m){physical[m]=physical[m&(m-1)]|(U(1)<<complement[low(m)]);
      if(__builtin_popcount(m)==5)rootRel[m]=relation(first,physical[m]);}
    uint64_t hits=0,candidates=0;
    for(const auto&t:templates){
      ++checked;
      std::array<Rel,6> r={rootRel[t.masks[0]],rootRel[t.masks[1]],rootRel[t.masks[2]],t.rs[0],t.rs[1],t.rs[2]};
      if(!r[0].allowed||!r[1].allowed||!r[2].allowed)continue;
      constexpr int left[6]={0,0,0,1,1,2},right[6]={1,2,3,2,3,3};
      std::array<U,4> cross={1,2,4,8};for(int e=0;e<6;++e)if(r[e].cross){cross[left[e]]|=U(1)<<right[e];cross[right[e]]|=U(1)<<left[e];}
      for(int mid=0;mid<4;++mid)for(int i=0;i<4;++i)if((cross[i]>>mid)&1)cross[i]|=cross[mid];
      if(cross[0]!=15)continue;
      auto find=[&](const std::array<int,4>*avoid,std::array<int,4>&out){
        for(int x=0;x<5;++x){if(avoid&&x==(*avoid)[0])continue;
          for(const auto&s:t.solutions){
            if(avoid&&(s[0]==(*avoid)[1]||s[1]==(*avoid)[2]||s[2]==(*avoid)[3]))continue;
            if(ok(r[0],x,s[0])&&ok(r[1],x,s[1])&&ok(r[2],x,s[2])){out={x,s[0],s[1],s[2]};return true;}
          }}return false;
      };
      std::array<int,4>a,b;if(!find(nullptr,a)||!find(&a,b))continue;++candidates;
      std::array<U,4> reach={1,2,4,8};
      for(int e=0;e<6;++e){int i=left[e],j=right[e];if(!ok(r[e],b[i],a[j]))reach[i]|=U(1)<<j;if(!ok(r[e],a[i],b[j]))reach[j]|=U(1)<<i;}
      for(int mid=0;mid<4;++mid)for(int i=0;i<4;++i)if((reach[i]>>mid)&1)reach[i]|=reach[mid];
      bool strong=true;for(U row:reach)strong&=row==15;
      if(strong)++hits;
      else {int start=0;while(reach[start]==15)++start;std::array<int,4>c;for(int i=0;i<4;++i)c[i]=((reach[start]>>i)&1)?b[i]:a[i];
        assert(c!=a&&c!=b);for(int e=0;e<6;++e)assert(ok(r[e],c[left[e]],c[right[e]]));}
    }
    weighted_survivors+=weight*hits;weighted_candidates+=weight*candidates;
    per<<first<<' '<<weight<<' '<<hits<<' '<<candidates<<'\n';
  }
  assert(orbits==406&&weights==15504&&weights*templates_all/4==488864376&&weighted_survivors%4==0);
  double elapsed=std::chrono::duration<double>(std::chrono::steady_clock::now()-started).count();
  std::cout<<"{\"status\":\"VERIFIED-COMP\",\"n\":20,\"classes\":4,\"all_partitions\":488864376,\"three_class_templates\":"<<templates_all<<",\"feasible_templates\":"<<templates.size()<<",\"first_block_orbits\":"<<orbits<<",\"completion_cases_checked\":"<<checked<<",\"weighted_survivors\":"<<weighted_survivors<<",\"survivors\":"<<weighted_survivors/4<<",\"weighted_candidate_pairs\":"<<weighted_candidates<<",\"seconds\":"<<elapsed<<"}\n";
  return weighted_survivors/4==415?0:2;
}
