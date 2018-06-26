#include <stdio.h>

int arr[10] = {0,};

int main(){
  int i = 100;
  int *p = &i;
  *p = 300;
  printf("%d", i);
  return 0;
}
