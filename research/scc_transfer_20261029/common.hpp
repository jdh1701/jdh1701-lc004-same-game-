#pragma once
#include <array>
#include <vector>
#include <fstream>
#include <iostream>
#include <cassert>
#include <cstdint>
#include <chrono>
using U=uint32_t;
struct Rel { U allowed=0; bool cross=false; };
std::array<Rel,1024> table;
int low(U m){return __builtin_ctz(m);}
Rel relation(U a,U b){
  U u=a|b, compressed=0;int rank=0;
  while(u){U bit=u&-u;if(a&bit)compressed|=U(1)<<rank;u-=bit;++rank;}
  assert(rank==10);return table[compressed];
}
bool ok(Rel r,int x,int y){return (r.allowed>>(5*x+y))&1;}
template<class F> void block5(U m,F f){
  int first=low(m);m&=m-1;std::vector<int> v;
  while(m){v.push_back(low(m));m&=m-1;}
  int n=v.size();
  for(int a=0;a<n;++a)for(int b=a+1;b<n;++b)
  for(int c=b+1;c<n;++c)for(int d=c+1;d<n;++d)
    f((U(1)<<first)|(U(1)<<v[a])|(U(1)<<v[b])|(U(1)<<v[c])|(U(1)<<v[d]));
}
struct Tmpl {std::array<U,3> masks;std::array<Rel,3> rs;std::vector<std::array<int,3>> solutions;};

std::vector<Tmpl> makeTemplates3(uint64_t&total){
  std::vector<Tmpl> templates;total=0;
  U full15=(U(1)<<15)-1;
  block5(full15,[&](U a){block5(full15^a,[&](U b){
    U c=full15^a^b;++total;
    Tmpl t; t.masks={a,b,c};t.rs={relation(a,b),relation(a,c),relation(b,c)};
    if(!t.rs[0].allowed||!t.rs[1].allowed||!t.rs[2].allowed)return;
    for(int x=0;x<5;++x)for(int y=0;y<5;++y)if(ok(t.rs[0],x,y))
      for(int z=0;z<5;++z)if(ok(t.rs[1],x,z)&&ok(t.rs[2],y,z))t.solutions.push_back({x,y,z});
    if(!t.solutions.empty())templates.push_back(std::move(t));
  });});
  return templates;
}
