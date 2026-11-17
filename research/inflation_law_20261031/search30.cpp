// Bounded obstruction search: insert one five-class into each of the 767
// previously verified n25 marked representatives. NOT a full n30 census.
#include "../scc_transfer_20261029/common.hpp"
#include <algorithm>
int main(int argc,char**argv){
 assert(argc==3);std::ifstream tin(std::string(argv[1])+"/geometry5.txt");assert(tin);
 for(auto&r:table){tin>>r.allowed>>r.cross;}
 assert(tin);
 std::ifstream in(std::string(argv[1])+"/survivor_witnesses_25.txt");assert(in);
 struct Parent{std::array<U,5> m;std::array<int,5>a,b;};std::vector<Parent> parents;
 Parent p;while(in>>p.m[0]){for(int i=1;i<5;++i)in>>p.m[i];for(int&x:p.a)in>>x;for(int&x:p.b)in>>x;assert(in);parents.push_back(p);}assert(parents.size()==767);
 std::ofstream witnesses(argv[2]);assert(witnesses);
 std::ofstream sample(std::string(argv[2])+".sample");assert(sample);
 uint64_t layouts=0,cases=0,survivor_completions=0,bad=0;const int pairEnds[5][2]={{0,1},{0,4},{1,2},{2,3},{3,4}};
 for(int a=0;a<26;++a)for(int b=a+1;b<27;++b)for(int c=b+1;c<28;++c)for(int d=c+1;d<29;++d)for(int e=d+1;e<30;++e){
  ++layouts;std::array<int,5> pos={a,b,c,d,e};U root=0;for(int x:pos)root|=U(1)<<x;
  std::array<int,25> rem{};int cnt=0;for(int i=0;i<30;++i)if(!(root>>i&1))rem[cnt++]=i;assert(cnt==25);
  std::array<U,5> pairMasks{};for(int s=0;s<5;++s)pairMasks[s]=(U(1)<<pos[pairEnds[s][0]])|(U(1)<<pos[pairEnds[s][1]]);
  for(const auto&P:parents){++cases;U A=31,B=31;bool crosses=false;std::array<U,5> phys{};
   for(int i=0;i<5;++i){U m=P.m[i];while(m){int k=low(m);m&=m-1;phys[i]|=U(1)<<rem[k];}
    auto r=relation(root,phys[i]);crosses|=r.cross;U ma=0,mb=0;
    for(int s=0;s<5;++s){if(ok(r,s,P.a[i]))ma|=1<<s;if(ok(r,s,P.b[i]))mb|=1<<s;}
    A&=ma;B&=mb;if(!A||!B)break;
   }
   if(!crosses||__builtin_popcount(A)!=1||__builtin_popcount(B)!=1||A==B)continue;
   ++survivor_completions;int x=low(A),y=low(B);bool uncovered=false;
   if(survivor_completions<=64){sample<<root;for(U m:phys)sample<<' '<<m;sample<<'\n';}
   for(int i=0;i<5;++i)if((pos[(i+1)%5]-pos[i]+30)%30==1){U edge=(U(1)<<pos[i])|(U(1)<<pos[(i+1)%5]);if(edge!=pairMasks[x]&&edge!=pairMasks[y])uncovered=true;}
   if(uncovered){++bad;witnesses<<root;for(U m:phys)witnesses<<' '<<m;witnesses<<' '<<x<<' '<<y<<'\n';}
  }
 }
 assert(layouts==142506&&cases==109302102);
 std::cout<<"{\"status\":\"VERIFIED-COMP\",\"parent_representatives\":"<<parents.size()<<",\"insertion_layouts_per_parent\":"<<layouts<<",\"completion_cases\":"<<cases<<",\"two_generator_survivor_completions\":"<<survivor_completions<<",\"uncovered_adjacent_pair_cases\":"<<bad<<",\"scope\":\"Bounded n30 insertion search; completions may duplicate patterns; not a full n30 census.\"}\n";
}
