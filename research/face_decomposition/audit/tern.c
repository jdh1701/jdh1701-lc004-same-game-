// Ternary hypothesis gates: rotation invariance, periodic words, losing orbit sizes, minimal residues
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#define MX 20
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
// minimal residue length reachable by genuine maximal-run moves (memo via hash on small words)
#include <stdint.h>
#define HS (1<<24)
uint64_t hk[HS]; signed char hv[HS];
uint64_t enc(const int*w,int n){ uint64_t k=n; for(int i=0;i<n;i++) k=k*3+w[i]; return k*2+1; }
int minres(const int*w,int n){
  uint64_t k=enc(w,n); uint64_t h=(k*0x9E3779B97F4A7C15ULL)>>40;
  while(hk[h] && hk[h]!=k) h=(h+1)&(HS-1);
  if(hk[h]==k) return hv[h];
  int best=n; int v[MX];
  int i=0; while(i<n){ int j=i; while(j<n&&w[j]==w[i]) j++;
    if(j-i>=2){ int m=0; for(int t=0;t<i;t++) v[m++]=w[t]; for(int t=j;t<n;t++) v[m++]=w[t];
      int r=minres(v,m); if(r<best) best=r; if(best==0) break; }
    i=j; }
  hk[h]=k; hv[h]=best; return best;
}
int main(int argc,char**argv){ int N=atoi(argv[1]);
  for(int n=2;n<=N;n++){
    long long total=1; for(int i=0;i<n;i++) total*=3;
    long long rotfail=0,losers=0,periodic_losers=0,per_total=0,resid[MX+1]; memset(resid,0,sizeof resid);
    int w[MX],r[MX];
    for(long long m=0;m<total;m++){ long long x=m; for(int i=0;i<n;i++){ w[i]=x%3; x/=3; }
      int W0=winword(w,n);
      // rotation invariance (one rotation suffices by induction)
      for(int i=0;i<n;i++) r[i]=w[(i+1)%n];
      if(winword(r,n)!=W0) rotfail++;
      // primitive period
      int p; for(p=1;p<n;p++){ if(n%p) continue; int ok=1; for(int i=p;i<n;i++) if(w[i]!=w[i-p]){ok=0;break;} if(ok) break; }
      if(p<n){ per_total++; if(!W0) periodic_losers++; }
      if(!W0){ losers++; if(n<=14) resid[minres(w,n)]++; }
    }
    printf("n=%d losers=%lld rot_fail=%lld periodic=%lld periodic_losers=%lld losers%%n=%lld",n,losers,rotfail,per_total,periodic_losers,(losers-periodic_losers)%n);
    if(n<=14){ printf(" residues:"); for(int t=1;t<=n;t++) if(resid[t]) printf(" %d:%lld",t,resid[t]); }
    printf("\n"); fflush(stdout);
  }
}
