#include <sys/types.h>
#include <stdio.h>
#include <dirent.h>
#include <string.h>

int main()
{
   DIR* dir_info;
   struct dirent *dir_entry, *dir_entry2;
   int len;
   
   dir_info = opendir(".");
   dir_entry = readdir(dir_info);
   len = strlen(dir_entry -> d_name);

   return 0;
}
