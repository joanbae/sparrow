#include <pwd.h>
#include <string.h>
#include <stdio.h>
#include <sys/types.h>

int main(int argc, char **argv)
{
  char str[100];
  
  struct passwd *pass_info =  getpwent();
  strncpy(str, pass_info->pw_name, 10);

  return 0;
}
