// brute force A(n,k): count RGS of length n (classes size>=2) that are winning.
// winning: interval DP W[i][j] = substring i..j-1 in grammar S -> e | c S c S | c S c S c S
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
int n; int w[32]; long long cnt[32]; int csize[32];
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
  // prune: number of classes with size 1 must be <= remaining positions
  int ones=0; for(int c=0;c<m;c++) if(csize[c]==1) ones++;
  if(ones > n-pos) return;
  if(pos==n){ if(ones==0 && win()) cnt[m]++; return; }
  for(int c=0;c<=m && c<16;c++){ w[pos]=c; csize[c]++; rec(pos+1, c==m?m+1:m); csize[c]--; }
}
int main(int argc,char**argv){ n=atoi(argv[1]); memset(csize,0,sizeof csize); rec(0,0);
  for(int k=1;k<=n/2;k++) printf("%lld ",cnt[k]); printf("\n"); }
