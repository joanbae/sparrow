#include <sys/types.h>
#include <dirent.h>
#include <stdio.h>
int main()
{
   DIR* dir_info;
   struct dirent *dir_entry, *dir_entry2;
   dir_info = opendir(".");
   dir_entry = readdir(dir_info);
   dir_entry2 = dir_entry + 500;

   char *file_name =  dir_entry2 -> d_name;
   
   return 0;
}
