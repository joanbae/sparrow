/* Haven't tried out this example yet but saving for the future. */
/* Use this example when it is the right time. */

#include <stdio.h>

int a_int[] = {0, 1, 2, 3, 4, 5, 6, 7, 8, 9,
	       10, 11, 12, 13, 14, 15, 16, 17,
	       18, 19, 20, 21, 22, 23, 24, 25};

int main(void)
{
  int *first = a_int;
  int *second = &a_int[5];
  int k = a_int[(void*)second - (void*)first + 100]; //BO
  return 0;
}
