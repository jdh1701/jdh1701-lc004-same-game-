#define _GNU_SOURCE
#include <dlfcn.h>
#include <string.h>
#include <stdio.h>
#include <unistd.h>
#include <stdlib.h>
ssize_t readlink(const char *p, char *b, size_t n) {
 static ssize_t (*real)(const char*,char*,size_t);
 if(!real) real=dlsym(RTLD_NEXT,"readlink");
 ssize_t r=real(p,b,n);
 char own[128]; snprintf(own,sizeof(own),"/proc/%d/exe",getpid());
 if(strcmp(p,"/proc/self/exe")==0 || strcmp(p,own)==0) {
  FILE *f=fopen("/proc/self/cmdline","rb"); char a[4096]; size_t i=0;
  if(f) { int c; while(i+1<sizeof(a) && (c=fgetc(f))>0) a[i++]=c; fclose(f); a[i]=0;
   char full[4096]; if(realpath(a,full) && access(full,X_OK)==0) { i=strlen(full); if(i>n)i=n; memcpy(b,full,i); return i; }
  }
 }
 return r;
}
