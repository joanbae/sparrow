/* Haven't tried out this example yet but saving for the future. */
/* Use this example when it is the right time. */

#include <stdio.h>

int a_int[] = {0, 1, 2, 3, 4, 5, 6, 7};

int main(void)
{
        int *first = a_int;
        int *second = first;
        while(*second != 5){
                second++;
        }
        printf("%d\n", second-first + 1); // result: 6
        printf("%d\n", (void*)second - (void*)first + 1); // result: 21
        return 0;
}
