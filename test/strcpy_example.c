#include <stdio.h>
#include <string.h>

int main ()
{
    char str1[]="Sample string";
    char str2[40] = "HI";
    char str3[40];

    strcpy(str2, str1);
    strcpy (str3,"copy successful");
    printf ("str1: %s\nstr2: %s\nstr3: %s\n",str1,str2,str3);
    return 0;
}

/* str2서는 오류가 난다고 하지만, str3에서는 오류가 안난다고 한다. */
/* 왜나면, constant string에 대해서는 정확한 nullpos를 계산하기 때문. */

