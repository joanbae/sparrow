#include <stdio.h>

int main ()
{
  char buffer [50];
  int n = 100, a=5, b=3;
  n=sprintf(buffer, "%d plus %d is %d", a, b, a+b); // case _ 에 해
  printf("%d and %c\n", n, buffer[n-1]);

  return 0;
}


/*
  On failure, a negative number is returned.
  하지만, 정확히 어떤 상황에서 음수를 내놓는다 라는 설명은 없다.
  지금 까지 찾은 경우 중 음수를 내 놓은 상황은,
  sprintf(buffer, NULL, NULL); 
*/
