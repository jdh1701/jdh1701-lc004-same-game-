// Complete two-generator first-excess search. SCC is a necessary filter only.
#include <algorithm>
#include <array>
#include <cassert>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <sstream>
#include <vector>
using V=std::vector<int>;using Part=std::vector<V>;
struct Type{V w,a,b;};struct G{V x,w;Part layer[2];};
std::vector<Type> types;std::vector<V> cats[7];std::vector<Part> parts[7];
std::array<unsigned,8> table[7][7][2048];
bool use_scc=true;
std::string data_dir;
int j,n,sixk,typeidnow;std::vector<G> gs;std::ofstream out;
std::uint64_t nodes[7]={},leaves[7]={},connected[7]={},positive[7]={},typenum[17]={};
bool cross(int a,int b,int c,int d){if(a>b)std::swap(a,b);if(c>d)std::swap(c,d);return(a<c&&c<b&&b<d)||(c<a&&a<d&&d<b);}
bool crossing(const V&a,const V&b){for(unsigned i=0;i<a.size();++i)for(unsigned k=i+1;k<a.size();++k)for(unsigned l=0;l<b.size();++l)for(unsigned m=l+1;m<b.size();++m)if(cross(a[i],a[k],b[l],b[m]))return true;return false;}
bool compat(const Part&a,const Part&b){for(auto&x:a)for(auto&y:b)if(crossing(x,y))return false;return true;}
Part placed(const V&xs,const V&labels){Part p(1+*std::max_element(labels.begin(),labels.end()));for(unsigned i=0;i<xs.size();++i)p[labels[i]].push_back(xs[i]);return p;}
void prepare(){
 std::ifstream f(data_dir+"/types.txt");int k;while(f>>k){Type t;t.w.resize(k);t.a.resize(k);t.b.resize(k);for(auto&x:t.w)f>>x;for(auto&x:t.a)f>>x;for(auto&x:t.b)f>>x;types.push_back(t);}assert(types.size()==17);
 std::ifstream c(data_dir+"/catalogues.txt");while(c>>k){V a(k);for(auto&x:a)c>>x;cats[k].push_back(a);V xs;for(int i=0;i<k;++i)xs.push_back(i);parts[k].push_back(placed(xs,a));}assert(cats[5].size()==5&&cats[6].size()==8);
 for(int a=5;a<=6;++a)for(int b=5;b<=6;++b)if(a+b<=11)for(int m=0;m<(1<<(a+b));++m)if(__builtin_popcount((unsigned)m)==a){
  V x,y;for(int i=0;i<a+b;++i)((m>>i&1)?x:y).push_back(i);
  for(unsigned s=0;s<cats[a].size();++s)for(unsigned t=0;t<cats[b].size();++t)if(compat(placed(x,cats[a][s]),placed(y,cats[b][t])))table[a][b][m][s]|=1u<<t;
 }
}
bool strong(){std::vector<unsigned> reach(j);for(int a=0;a<j;++a){reach[a]=1u<<a;for(int b=0;b<j;++b)if(!compat(gs[a].layer[1],gs[b].layer[0]))reach[a]|=1u<<b;}for(int k=0;k<j;++k)for(int a=0;a<j;++a)if(reach[a]>>k&1)reach[a]|=reach[k];for(auto r:reach)if(r!=(1u<<j)-1)return false;return true;}
bool conn(){unsigned seen=1;for(;;){unsigned old=seen;for(int a=0;a<j;++a)if(seen>>a&1)for(int b=0;b<j;++b)if(!(seen>>b&1)&&crossing(gs[a].x,gs[b].x))seen|=1u<<b;if(old==seen)return seen==(1u<<j)-1;}}
bool exactlytwo(V&p){
 V col(n,-1),weight(n);for(int a=0;a<j;++a)for(unsigned k=0;k<gs[a].x.size();++k){int x=gs[a].x[k];assert(col[x]==-1);col[x]=a;weight[x]=gs[a].w[k];}
 std::vector<V> loc(j);int pos=0;for(int i=0;i<n;++i)for(int k=0;k<weight[i];++k){loc[col[i]].push_back(pos++);p.push_back(col[i]);}assert(pos==5*j+1);
 std::vector<std::vector<std::array<unsigned,8>>> rel(j,std::vector<std::array<unsigned,8>>(j));
 for(int a=0;a<j;++a)for(int b=0;b<a;++b){unsigned m=0;unsigned ia=0,ib=0;int na=loc[a].size(),nb=loc[b].size();for(int k=0;k<na+nb;++k){if(ia<loc[a].size()&&(ib==loc[b].size()||loc[a][ia]<loc[b][ib])){m|=1u<<k;++ia;}else ++ib;}rel[a][b]=table[na][nb][m];for(unsigned s=0;s<cats[na].size();++s)for(unsigned t=0;t<cats[nb].size();++t)if(rel[a][b][s]>>t&1)rel[b][a][t]|=1u<<s;}
 V assign(j,-1);int solutions=0;
 auto solve=[&](auto&&self,int depth)->void{if(solutions>2)return;if(depth==j){++solutions;return;}int best=-1,size=9;unsigned domain=0;for(int a=0;a<j;++a)if(assign[a]<0){unsigned d=(1u<<cats[loc[a].size()].size())-1;for(int b=0;b<j;++b)if(assign[b]>=0)d&=rel[b][a][assign[b]];int z=__builtin_popcount(d);if(!z)return;if(z<size){best=a;size=z;domain=d;}}for(unsigned s=0;s<cats[loc[best].size()].size();++s)if(domain>>s&1){assign[best]=s;self(self,depth+1);assign[best]=-1;if(solutions>2)return;}};
 solve(solve,0);assert(solutions>=2);return solutions==2;
}
bool adjacent(int a,int b){return(a+1)%n==b||(b+1)%n==a;}
void visit(std::uint64_t used){
 ++nodes[sixk];if((int)gs.size()==j){++leaves[sixk];if(!conn())return;++connected[sixk];if(use_scc&&!strong())return;V p;if(!exactlytwo(p))return;++positive[sixk];++typenum[typeidnow];if(out.is_open()){out<<sixk<<' '<<typeidnow;for(int a:p)out<<' '<<a;out<<'\n';}return;}
 int a=0;while(used>>a&1)++a;
 for(int b=a+1;b<n;++b)if(!(used>>b&1)&&!adjacent(a,b))for(int c=b+1;c<n;++c)if(!(used>>c&1)&&!adjacent(a,c)&&!adjacent(b,c)){
  V x={a,b,c};for(int r=0;r<3;++r){int e[2],z=0;for(int k=0;k<3;++k)if(k!=r)e[z++]=k;for(int o=0;o<2;++o){G g;g.x=x;g.w={2,2,2};g.w[r]=1;g.layer[0]={{x[r],x[e[o]]},{x[e[1-o]]}};g.layer[1]={{x[r],x[e[1-o]]},{x[e[o]]}};bool ok=true;for(auto&t:gs)if(!compat(g.layer[0],t.layer[0])||!compat(g.layer[1],t.layer[1])){ok=false;break;}if(!ok)continue;gs.push_back(g);visit(used|(1ULL<<a)|(1ULL<<b)|(1ULL<<c));gs.pop_back();}}
 }
}
int main(int argc,char**argv){if(argc<4||argc>5)return 2;j=std::stoi(argv[1]);data_dir=argv[2];if(j<2||j>9)return 2;out.open(argv[3]);assert(out);if(argc==5){assert(std::string(argv[4])=="no-scc");use_scc=false;}prepare();for(typeidnow=0;typeidnow<(int)types.size();++typeidnow){auto&t=types[typeidnow];sixk=t.w.size();n=3*(j-1)+sixk;V x;auto choose=[&](auto&&self,int next,std::uint64_t mask)->void{if((int)x.size()==sixk){G g;g.x=x;g.w=t.w;g.layer[0]=placed(x,t.a);g.layer[1]=placed(x,t.b);gs.push_back(g);visit(mask);gs.pop_back();return;}for(int at=next;at<=n-(sixk-(int)x.size());++at){x.push_back(at);self(self,at+1,mask|(1ULL<<at));x.pop_back();}};choose(choose,0,0);std::cerr<<"type "<<typeidnow<<" accepted "<<typenum[typeidnow]<<'\n';}
 std::cout<<"{\"classes\":"<<j<<",\"layers\":[";std::uint64_t total=0;for(int k:{4,6}){auto scaled=positive[k]*(5*j+1);assert(scaled%(3*(j-1)+k)==0);auto count=scaled/(3*(j-1)+k);total+=count;std::cout<<(k==6?",":"")<<"{\"six_core_vertices\":"<<k<<",\"nodes\":"<<nodes[k]<<",\"pairs\":"<<leaves[k]<<",\"connected\":"<<connected[k]<<",\"accepted\":"<<positive[k]<<",\"original_patterns\":"<<count<<"}";}std::cout<<"],\"two_generator_first_excess\":"<<total<<",\"accepted_by_type\":[";for(int a=0;a<17;++a)std::cout<<(a?",":"")<<typenum[a];std::cout<<"]}\n";
}
