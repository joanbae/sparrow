#include <stdio.h>
#include <string.h>

int main ()
{
    char str1[]="Sample string";
    char str2[40];
    strcpy(str2,str1);
    return 0;
}

/* str2서는 오류가 난다고 하지만, str3에서는 오류가 안난다고 한다. */
/* 왜나면, constant string에 대해서는 정확한 nullpos를 계산하기 때문. */

