// binary winning words by content (a = #0s, b = #1s), n<=MAXN
#include <stdio.h>
#include <stdlib.h>
#define MX 32
static unsigned char Wt[MX+1][MX+1];
int winword(const int*w,int n){
  for(int len=0;len<=n;len++) for(int i=0;i+len<=n;i++){
    int j=i+len; if(len==0){Wt[i][j]=1;continue;}
    int ok=0,c=w[i];
    for(int a=i+1;a<j&&!ok;a++) if(w[a]==c&&Wt[i+1][a]){
      if(Wt[a+1][j]) ok=1;
      for(int b=a+1;b<j&&!ok;b++) if(w[b]==c&&Wt[a+1][b]&&Wt[b+1][j]) ok=1;
    }
    Wt[i][j]=ok;
  }
  return Wt[0][n];
}
int main(int argc,char**argv){ int N=atoi(argv[1]);
  static long long cnt[MX+1][MX+1];
  for(int n=1;n<=N;n++){ int w[MX];
    for(long long m=0;m<(1LL<<n);m++){ int ones=0; for(int i=0;i<n;i++){ w[i]=(m>>i)&1; ones+=w[i]; }
      if(winword(w,n)) cnt[n-ones][ones]++; } }
  for(int a=0;a<=N;a++){ for(int b=0;a+b<=N;b++) printf("%lld ",cnt[a][b]); printf("\n"); }
}
