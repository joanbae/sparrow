#include <sys/types.h>
#include <dirent.h>

int main()
{
   DIR* dir_info;
   dir_info = opendir(".");
   char* p = (char*)readdir(dir_info);
   p[1] = 1;

   return 0;
}
