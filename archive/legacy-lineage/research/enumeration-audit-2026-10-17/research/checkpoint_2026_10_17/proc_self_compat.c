/* Runtime-only compatibility for hosts allowing /proc/self/exe but denying
   /proc/<own-numeric-pid>/exe. Does not alter Lean or any proof-checking code.
   Only the current process's executable lookup is redirected. */
#define _GNU_SOURCE
#include <dlfcn.h>
#include <stdio.h>
#include <string.h>
#include <unistd.h>

ssize_t readlink(const char *path, char *buf, size_t size) {
    static ssize_t (*real_readlink)(const char *, char *, size_t);
    if (!real_readlink) real_readlink = dlsym(RTLD_NEXT, "readlink");
    char own[64];
    snprintf(own, sizeof own, "/proc/%d/exe", (int)getpid());
    return real_readlink(strcmp(path, own) == 0 ? "/proc/self/exe" : path, buf, size);
}
