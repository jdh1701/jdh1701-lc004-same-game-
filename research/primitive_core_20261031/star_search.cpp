#include <algorithm>
#include <array>
#include <chrono>
#include <cstdint>
#include <cstdlib>
#include <fstream>
#include <iostream>
#include <vector>

struct Star { int x[3], root, up, down; };
int classes, n;
std::vector<Star> stars;
std::uint64_t nodes=0, leaves=0, connected=0, strong=0;
std::ofstream witnesses;

bool cross(int a,int b,int c,int d) {
  if(a>b)std::swap(a,b);
  if(c>d)std::swap(c,d);
  return (a<c&&c<b&&b<d)||(c<a&&a<d&&d<b);
}
bool triple_cross(const Star&a,const Star&b) {
  for(int i=0;i<3;++i)for(int j=i+1;j<3;++j)
    for(int k=0;k<3;++k)for(int l=k+1;l<3;++l)
      if(cross(a.x[i],a.x[j],b.x[k],b.x[l]))return true;
  return false;
}
bool is_connected() {
  std::uint64_t seen=1;
  for(;;) {
    auto old=seen;
    for(int i=0;i<classes;++i)if(seen>>i&1)
      for(int j=0;j<classes;++j)if(!(seen>>j&1)&&triple_cross(stars[i],stars[j]))seen|=1ULL<<j;
    if(seen==old)return seen==((1ULL<<classes)-1);
  }
}
bool adjacent(int a,int b){return (a+1)%n==b||(b+1)%n==a;}
bool is_strong() {
  std::vector<std::uint64_t> reach(classes);
  for(int i=0;i<classes;++i) {
    reach[i]=1ULL<<i;
    for(int j=0;j<classes;++j)
      if(cross(stars[i].root,stars[i].down,stars[j].root,stars[j].up))reach[i]|=1ULL<<j;
  }
  for(int k=0;k<classes;++k)for(int i=0;i<classes;++i)if(reach[i]>>k&1)reach[i]|=reach[k];
  for(auto r:reach)if(r!=((1ULL<<classes)-1))return false;
  return true;
}
void visit(std::uint64_t used) {
  ++nodes;
  if((int)stars.size()==classes) {
    ++leaves;
    if(!is_connected())return;
    ++connected;
    if(!is_strong())return;
    ++strong;
    if(witnesses.is_open()) {
      for(const auto&s:stars) witnesses<<s.x[0]<<' '<<s.x[1]<<' '<<s.x[2]<<' '<<s.root<<' '<<s.up<<' '<<s.down<<' ';
      witnesses<<'\n';
    }
    return;
  }
  int a=0;while(used>>a&1)++a;
  for(int b=a+1;b<n;++b)if(!(used>>b&1)&&!adjacent(a,b))
    for(int c=b+1;c<n;++c)if(!(used>>c&1)&&!adjacent(a,c)&&!adjacent(b,c)) {
      int x[3]={a,b,c};
      for(int r=0;r<3;++r) {
        int e[2],k=0;for(int i=0;i<3;++i)if(i!=r)e[k++]=x[i];
        for(int o=0;o<(stars.empty()?1:2);++o) {
          Star s{{a,b,c},x[r],e[o],e[1-o]};
          bool ok=true;
          for(const auto&t:stars)if(cross(s.root,s.up,t.root,t.up)||cross(s.root,s.down,t.root,t.down)){ok=false;break;}
          if(!ok)continue;
          stars.push_back(s);visit(used|(1ULL<<a)|(1ULL<<b)|(1ULL<<c));stars.pop_back();
        }
      }
    }
}
int main(int argc,char**argv) {
  if(argc<2||argc>3)return 2;
  classes=std::atoi(argv[1]);n=3*classes;
  if(classes<2||classes>20)return 2;
  if(argc==3){witnesses.open(argv[2]);if(!witnesses)return 2;}
  auto start=std::chrono::steady_clock::now();
  visit(0);
  std::cerr<<"seconds "<<std::chrono::duration<double>(std::chrono::steady_clock::now()-start).count()<<'\n';
  std::cout<<"{\"classes\":"<<classes<<",\"nodes\":"<<nodes<<",\"proper_star_pairs\":"<<leaves<<",\"connected_proper_star_pairs\":"<<connected<<",\"strong_star_pairs\":"<<strong<<",\"all_five_survivors\":"<<strong*5/3<<",\"orbit_weight_integral\":"<<(strong%3==0?"true":"false")<<"}\n";
}
