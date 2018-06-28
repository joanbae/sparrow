#include <stdio.h>

typedef struct _charVoid
{
  int numbers[16];
} charVoid;

charVoid str;

int main(){
  *((int *)&str+100000) = 500;
  int c =  str.numbers[100];
  printf("%d\n", c);
  return 0;
}


/* 11번 -> str = [500, 500]으로 계산 */
/* BO 알람도 안남.   */
