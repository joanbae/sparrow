#include <stdio.h>

int main(){
 
  int a[10] = {0,};
  unsigned int k = 4294967295;
  int t = (int)k;
  a[t+1] = 1;
  printf("%d\n", t);


}

 /* 이 예제는 다음과 같은 이유로 해당 되지 않는다. 
 
    1 When a value with integer type is converted to another integer type other than _Bool, if
    the value can be represented by the new type, it is unchanged.
    2 Otherwise, if the new type is unsigned, the value is converted by repeatedly adding or
    subtracting one more than the maximum value that can be represented in the new type
    until the value is in the range of the new type.49)
    3 Otherwise, the new type is signed and the value cannot be represented in it; either the
    result is implementation-defined or an implementation-defined signal is raised.
*/
