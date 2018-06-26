#include <stdio.h>

int main ()
{
  char buffer [50];
  int n = 100, a=5, b=3;
  n=sprintf(buffer, "Hello World in Ocaml"); // case 1번에 해당
  printf("%d and %c\n", n, buffer[n-1]);
  return 0;
}


/*
  bug fix 전에 커밋으로 돌려놓고 컴파일 하면 
  buffer overrun이 있다고 한다. 
*/
