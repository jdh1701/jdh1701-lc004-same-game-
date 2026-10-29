// Count winning RGS of length n with exactly K classes (no singleton classes), sharded.
// usage: bf_k n K shards shard   (shard split at depth D by prefix counter)
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
int n,K,T,R; int w[32]; int csize[32]; long long cnt=0, pref=0; const int D=9;
static unsigned char W[33][33];
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
void rec(int pos,int m){
  if(m>K || m+(n-pos)<K) return;
  int ones=0; for(int c=0;c<m;c++) if(csize[c]==1) ones++;
  if(ones>n-pos) return;
  if(pos==D){ if((pref++)%T!=R) return; }
  if(pos==n){ if(m==K && ones==0 && win()) cnt++; return; }
  for(int c=0;c<=m;c++){ w[pos]=c; csize[c]++; rec(pos+1,c==m?m+1:m); csize[c]--; }
}
int main(int argc,char**argv){ n=atoi(argv[1]);K=atoi(argv[2]);T=atoi(argv[3]);R=atoi(argv[4]);
  rec(0,0); printf("%d %d %d %d %lld\n",n,K,T,R,cnt); return 0; }
