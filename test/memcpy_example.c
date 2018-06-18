#include <string.h>
#include <stdio.h>

typedef struct _charVoid
{
  char charFirst[16];
  void * voidSecond;
  void * voidThird;
} charVoid;

int main()
{
  charVoid s;
  char str[] = "hello world in ocaml";
  memcpy (s.charFirst, str, strlen(str));
  printf("s.charFirst: %s\n",s.charFirst);
}

