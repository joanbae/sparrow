#include <stdio.h>
int main(){
  int a[1];
  int k = -1;
  int t = (int)(unsigned int)k;
  a[t+1] = 0;
   return 0;
}
