#include <process.h>
#include <string.h>
#include <stdlib.h>

int main(int argc, char** argv) {
    char** new_argv = malloc((argc + 2) * sizeof(char*));
    int new_argc = 0;
    new_argv[new_argc++] = "clang";
    for (int i = 1; i < argc; i++) {
        if (strcmp(argv[i], "-fPIC") != 0) {
            new_argv[new_argc++] = argv[i];
        }
    }
    new_argv[new_argc++] = "-mno-stack-arg-probe";
    new_argv[new_argc] = NULL;
    return _spawnv(_P_WAIT, "C:\\Program Files\\clang+llvm-18.1.8-x86_64-pc-windows-msvc\\bin\\clang.exe", (const char* const*)new_argv);
}
