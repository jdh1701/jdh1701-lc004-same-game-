// G1: direct counterexample search for the face lemma.
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#define MX 96
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
int face_criterion(const int*w,int n){
  int size[MX]={0}; for(int i=0;i<n;i++) size[w[i]]++;
  for(int i=0;i<n;i++) if(size[w[i]]==1) return 0;
  // rigid NC: no a<b<c<d with w[a]==w[c], w[b]==w[d], distinct rigid classes
  for(int a=0;a<n;a++) if(size[w[a]]<=3) for(int b=a+1;b<n;b++) if(size[w[b]]<=3 && w[b]!=w[a])
    for(int c=b+1;c<n;c++) if(w[c]==w[a]) for(int d=c+1;d<n;d++) if(w[d]==w[b]) return 0;
  // heavy positions and faces
  int hp[MX],H=0; for(int i=0;i<n;i++) if(size[w[i]]>=4) hp[H++]=i;
  int face[MX]; for(int i=0;i<H;i++) face[i]=-1;
  int nf=0;
  for(int i=0;i<H;i++){ if(face[i]>=0) continue; face[i]=nf;
    for(int j=i+1;j<H;j++) if(face[j]<0){
      // same face iff no rigid class has points both inside (hp[i],hp[j]) and outside
      int sep=0;
      for(int c=0;c<n && !sep;c++){ // class id c
        if(size[c]<2||size[c]>3) continue;
        int in=0,out=0;
        for(int t=0;t<n;t++) if(w[t]==c){ if(t>hp[i]&&t<hp[j]) in=1; else out=1; }
        if(in&&out) sep=1;
      }
      if(!sep) face[j]=nf;
    }
    nf++;
  }
  for(int f=0;f<nf;f++){ int fw[MX],m=0; for(int i=0;i<H;i++) if(face[i]==f) fw[m++]=w[hp[i]];
    if(!winword(fw,m)) return 0; }
  return 1;
}
int N; int ww[MX]; int cs[MX]; long long tested=0,mism=0,wins=0;
void rec(int pos,int m){
  if(pos==N){ int c=winword(ww,N), f=face_criterion(ww,N); tested++; wins+=c; if(c!=f) mism++; return; }
  for(int c=0;c<=m && c<MX;c++){ ww[pos]=c; rec(pos+1,c==m?m+1:m); }
}
int main(int argc,char**argv){ for(N=1;N<=atoi(argv[1]);N++){ tested=mism=wins=0; rec(0,0); printf("n=%d all patterns=%lld winners=%lld mismatches=%lld\n",N,tested,wins,mism); fflush(stdout);} }
