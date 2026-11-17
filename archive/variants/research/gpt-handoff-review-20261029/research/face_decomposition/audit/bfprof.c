// brute force per-profile counts of winning patterns of length n
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
int n; int w[40]; int csize[40];
static unsigned char W[41][41];
#define HS (1<<20)
unsigned long long keys[HS]; long long vals[HS];
int win(){
  for(int len=0;len<=n;len++) for(int i=0;i+len<=n;i++){
    int j=i+len; if(len==0){W[i][j]=1;continue;}
    int ok=0; int c=w[i];
    for(int a=i+1;a<j && !ok;a++) if(w[a]==c && W[i+1][a]){
      if(W[a+1][j]) ok=1;
      for(int b=a+1;b<j && !ok;b++) if(w[b]==c && W[a+1][b] && W[b+1][j]) ok=1;
    }
    W[i][j]=ok;
  }
  return W[0][n];
}
void add(unsigned long long key){
  unsigned long long h=(key*0x9E3779B97F4A7C15ULL)>>44;
  while(keys[h] && keys[h]!=key) h=(h+1)&(HS-1);
  keys[h]=key; vals[h]++;
}
void rec(int pos,int m){
  int ones=0; for(int c=0;c<m;c++) if(csize[c]==1) ones++;
  if(ones > n-pos) return;
  if(pos==n){ if(ones==0 && win()){
      int hist[41]={0}; for(int c=0;c<m;c++) hist[csize[c]]++;
      unsigned long long key=0; // base-17 digits, sizes 2..n (fits 64 bits for n<=16)
      for(int s=2;s<=n;s++){ key=key*17+hist[s]; }
      add(key);
    } return; }
  for(int c=0;c<=m && c<20;c++){ w[pos]=c; csize[c]++; rec(pos+1, c==m?m+1:m); csize[c]--; }
}
int main(int argc,char**argv){ n=atoi(argv[1]); rec(0,0);
  for(int h=0;h<HS;h++) if(keys[h]){
    unsigned long long key=keys[h]; int hist[41];
    for(int s=n;s>=2;s--){ hist[s]=key%17; key/=17; }
    for(int s=2;s<=n;s++) if(hist[s]) printf("%d:%d ",s,hist[s]);
    printf("= %lld\n",vals[h]);
  }
}
