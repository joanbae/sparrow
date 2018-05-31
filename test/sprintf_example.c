#include <stdio.h>

int main ()
{
  char buffer [50];
  int n, a=5, b=3;
  n=sprintf (buffer, "%d plus %d is %d", a, b, a+b);

  printf("%d and %c\n", n, buffer[n-1]);
  sparrow_print(n);
  sparrow_print(buffer);
  return 0;
}

