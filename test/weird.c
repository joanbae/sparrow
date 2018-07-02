#include <stdio.h>

typedef struct _charVoid
{
  int numbers[16];
} charVoid;

charVoid str;

int main(){
  charVoid* str2 = (charVoid*)malloc(sizeof(charVoid));

  *((int *)&str+10000) = 500;
  *((int *)str2+10000) = 500;
  int c =  str.numbers[100000];
  int c =  str2->numbers[100000];
  printf("%d\n", c);
  return 0;
}


/* 11번 -> str = [500, 500]으로 계산 */
/* BO 알람도 안남.   */
/* With our current design of Sparrow, analysis can't be done on this code*/
