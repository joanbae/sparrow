#include <stdio.h>
#include <string.h>

int main ()
{
    char str[] = "This is a sample string";
    char * pch;
    pch=strchr(str,'s');
    char c = str[pch-str];
    sparrow_print(pch);
    sparrow_print(str);
    sparrow_print(c);
    return 0;
}
