#include "common.hpp"
struct Tmpl4 {
  std::array<U,4> masks;
  std::array<Rel,6> rs;
  std::vector<uint16_t> solutions;
  std::array<uint8_t,4> components{};int ncomponents=0;
};
constexpr int L4[6]={0,0,0,1,1,2},R4[6]={1,2,3,2,3,3};
int main(int argc,char**argv){
  assert(argc==2);std::string dir=argv[1];std::ifstream tin(dir+"/geometry5.txt");assert(tin.good());
  for(auto&r:table){int c;tin>>r.allowed>>c;r.cross=c;}assert(tin.good());
  auto started=std::chrono::steady_clock::now();uint64_t all3=0;auto small=makeTemplates3(all3);
  uint64_t incidences3=0;for(const auto&t:small)incidences3+=t.solutions.size();
  assert(all3==126126&&small.size()==13355&&incidences3==60060);
  std::vector<Tmpl4> templates;uint64_t incidences4=0;
  std::vector<U> physical(1<<20);std::vector<Rel> rootRel(1<<20);
  U full20=(U(1)<<20)-1;
  block5(full20,[&](U first){
    std::array<int,15> complement{};int n=0;for(int i=0;i<20;++i)if(!((first>>i)&1))complement[n++]=i;assert(n==15);
    physical[0]=0;for(U m=1;m<(U(1)<<15);++m){physical[m]=physical[m&(m-1)]|(U(1)<<complement[low(m)]);if(__builtin_popcount(m)==5)rootRel[m]=relation(first,physical[m]);}
    for(const auto&t:small){
      Rel r0=rootRel[t.masks[0]],r1=rootRel[t.masks[1]],r2=rootRel[t.masks[2]];
      if(!r0.allowed||!r1.allowed||!r2.allowed)continue;
      Tmpl4 next;next.masks={first,physical[t.masks[0]],physical[t.masks[1]],physical[t.masks[2]]};next.rs={r0,r1,r2,t.rs[0],t.rs[1],t.rs[2]};
      for(int x=0;x<5;++x)for(const auto&s:t.solutions)if(ok(r0,x,s[0])&&ok(r1,x,s[1])&&ok(r2,x,s[2]))next.solutions.push_back(x|(s[0]<<3)|(s[1]<<6)|(s[2]<<9));
      if(next.solutions.empty())continue;
      incidences4+=next.solutions.size();std::array<U,4> reach={1,2,4,8};
      for(int e=0;e<6;++e)if(next.rs[e].cross){reach[L4[e]]|=U(1)<<R4[e];reach[R4[e]]|=U(1)<<L4[e];}
      for(int mid=0;mid<4;++mid)for(int i=0;i<4;++i)if((reach[i]>>mid)&1)reach[i]|=reach[mid];
      U covered=0;for(int i=0;i<4;++i)if(!((covered>>i)&1)){next.components[next.ncomponents++]=reach[i];covered|=reach[i];}
      templates.push_back(std::move(next));
    }
  });
  assert(incidences4==16279200);
  std::cerr<<"Templates4="<<templates.size()<<" incidences4="<<incidences4<<"\n";
  std::ifstream oin(dir+"/first_block_orbits_25.txt");assert(oin.good());
  std::ofstream per(dir+"/orbit_results_25.txt"),positive(dir+"/survivor_witnesses_25.txt");
  uint64_t total=0,checked=0,orbits=0,weights=0,candidate_total=0;U first;int weight;
  while(oin>>first>>weight){
    ++orbits;weights+=weight;std::array<int,20> complement{};int n=0;for(int i=0;i<25;++i)if(!((first>>i)&1))complement[n++]=i;assert(n==20);
    physical[0]=0;for(U m=1;m<(U(1)<<20);++m){physical[m]=physical[m&(m-1)]|(U(1)<<complement[low(m)]);if(__builtin_popcount(m)==5)rootRel[m]=relation(first,physical[m]);}
    uint64_t hits=0,candidates=0;
    for(const auto&t:templates){
      ++checked;std::array<Rel,4> root={rootRel[t.masks[0]],rootRel[t.masks[1]],rootRel[t.masks[2]],rootRel[t.masks[3]]};
      if(!root[0].allowed||!root[1].allowed||!root[2].allowed||!root[3].allowed)continue;
      U cross=0;for(int q=0;q<4;++q)if(root[q].cross)cross|=U(1)<<q;
      bool connected=true;for(int q=0;q<t.ncomponents;++q)connected&=(cross&t.components[q])!=0;if(!connected)continue;
      auto find=[&](const std::array<int,5>*avoid,std::array<int,5>&out){
        for(int x=0;x<5;++x){if(avoid&&x==(*avoid)[0])continue;
          for(uint16_t code:t.solutions){std::array<int,5> c={x,code&7,(code>>3)&7,(code>>6)&7,(code>>9)&7};bool valid=true;
            for(int q=0;q<4;++q)if((avoid&&c[q+1]==(*avoid)[q+1])||!ok(root[q],x,c[q+1])){valid=false;break;}
            if(valid){out=c;return true;}
          }}return false;
      };
      std::array<int,5>a,b;if(!find(nullptr,a)||!find(&a,b))continue;++candidates;
      std::array<U,5> reach={1,2,4,8,16};
      for(int q=0;q<4;++q){if(!ok(root[q],b[0],a[q+1]))reach[0]|=U(1)<<(q+1);if(!ok(root[q],a[0],b[q+1]))reach[q+1]|=1;}
      for(int e=0;e<6;++e){int i=L4[e]+1,j=R4[e]+1;if(!ok(t.rs[e],b[i],a[j]))reach[i]|=U(1)<<j;if(!ok(t.rs[e],a[i],b[j]))reach[j]|=U(1)<<i;}
      for(int mid=0;mid<5;++mid)for(int i=0;i<5;++i)if((reach[i]>>mid)&1)reach[i]|=reach[mid];
      bool strong=true;for(U row:reach)strong&=row==31;
      if(strong){++hits;positive<<first;for(int q=0;q<4;++q)positive<<' '<<physical[t.masks[q]];for(int x:a)positive<<' '<<x;for(int x:b)positive<<' '<<x;positive<<'\n';}
      else {int start=0;while(reach[start]==31)++start;std::array<int,5>c;for(int i=0;i<5;++i)c[i]=((reach[start]>>i)&1)?b[i]:a[i];assert(c!=a&&c!=b);
        for(int q=0;q<4;++q){assert(ok(root[q],c[0],c[q+1]));}
        for(int e=0;e<6;++e){assert(ok(t.rs[e],c[L4[e]+1],c[R4[e]+1]));}
      }
    }
    total+=weight*hits;candidate_total+=candidates;per<<first<<' '<<weight<<' '<<hits<<' '<<candidates<<'\n';
    if(orbits%100==0)std::cerr<<"orbits="<<orbits<<" weighted_survivors="<<total<<"\n";
  }
  assert(weights==53130&&total%5==0);
  double elapsed=std::chrono::duration<double>(std::chrono::steady_clock::now()-started).count();
  std::cout<<"{\"status\":\"VERIFIED-COMP\",\"n\":25,\"classes\":5,\"templates4\":"<<templates.size()<<",\"certificate_incidences4\":"<<incidences4<<",\"first_block_orbits\":"<<orbits<<",\"orbit_weight_sum\":"<<weights<<",\"completion_cases_checked\":"<<checked<<",\"candidate_pairs_checked\":"<<candidate_total<<",\"weighted_survivors\":"<<total<<",\"survivors\":"<<total/5<<",\"seconds\":"<<elapsed<<"}\n";
}
