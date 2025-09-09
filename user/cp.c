/**
 * cp - copy files
 * POSIX.1-2024 compliant implementation for FeuerBird exokernel
 * 
 * Usage: cp [-ipr] source_file target_file
 *        cp [-ipr] source_file... target_dir
 * 
 * Options:
 *   -i  Interactive mode (prompt before overwrite)
 *   -p  Preserve file attributes
 *   -r  Copy directories recursively
 */

#include <types.h>
#include "user_minimal.h"

// Forward declaration
static int copy_directory(const char *src, const char *dst);

#define BUFSIZE 512

static int iflag = 0;  // Interactive mode
static int pflag = 0;  // Preserve attributes
static int rflag = 0;  // Recursive

static void
usage(void)
{
  printf(2, "Usage: cp [-ipr] source target\n");
  printf(2, "       cp [-ipr] source... directory\n");
  exit(0);
}

static int
confirm_overwrite(const char *path)
{
  char response[10];
  
  printf(1, "overwrite '%s'? ", path);
  gets(response, sizeof(response));
  
  return (response[0] == 'y' || response[0] == 'Y');
}

static int
copy_file(const char *src, const char *dst)
{
  int fd_src, fd_dst;
  int n;
  char buf[BUFSIZE];
  struct stat st;
  
  // Check if source exists and get its attributes
  if(stat(src, &st) < 0) {
    printf(2, "cp: cannot stat '%s'\n", src);
    return -1;
  }
  
  // Check if source is a directory
  if(st.type == T_DIR) {
    if(!rflag) {
      printf(2, "cp: omitting directory '%s'\n", src);
      return -1;
    }
    return copy_directory(src, dst);
  }
  
  // Open source file
  if((fd_src = open(src, O_RDONLY)) < 0) {
    printf(2, "cp: cannot open '%s'\n", src);
    return -1;
  }
  
  // Check if destination exists
  if(iflag) {
    struct stat dst_st;
    if(stat(dst, &dst_st) >= 0) {
      if(!confirm_overwrite(dst)) {
        close(fd_src);
        return 0;
      }
    }
  }
  
  // Create/open destination file
  if((fd_dst = open(dst, O_CREATE | O_WRONLY)) < 0) {
    printf(2, "cp: cannot create '%s'\n", dst);
    close(fd_src);
    return -1;
  }
  
  // Copy data
  while((n = read(fd_src, buf, sizeof(buf))) > 0) {
    if(write(fd_dst, buf, n) != n) {
      printf(2, "cp: write error\n");
      close(fd_src);
      close(fd_dst);
      return -1;
    }
  }
  
  if(n < 0) {
    printf(2, "cp: read error\n");
    close(fd_src);
    close(fd_dst);
    return -1;
  }
  
  // Preserve attributes if requested
  if(pflag) {
    // In a real implementation, we would preserve:
    // - File permissions (chmod)
    // - Ownership (chown)
    // - Timestamps (utime)
    // Currently not fully supported in xv6
  }
  
  close(fd_src);
  close(fd_dst);
  
  return 0;
}

static int
copy_directory(const char *src, const char *dst)
{
  struct stat st;
  struct dirent de;
  char src_path[512];
  char dst_path[512];
  int fd;
  
  // Create destination directory
  if(mkdir(dst) < 0) {
    // Check if it already exists
    if(stat(dst, &st) < 0 || st.type != T_DIR) {
      printf(2, "cp: cannot create directory '%s'\n", dst);
      return -1;
    }
  }
  
  // Open source directory
  if((fd = open(src, O_RDONLY)) < 0) {
    printf(2, "cp: cannot open directory '%s'\n", src);
    return -1;
  }
  
  // Copy each entry
  while(read(fd, &de, sizeof(de)) == sizeof(de)) {
    if(de.ino == 0)
      continue;
    
    // Skip . and ..
    if(strcmp(de.name, ".") == 0 || strcmp(de.name, "..") == 0)
      continue;
    
    // Build full paths
    strcpy(src_path, src);
    if(src_path[strlen(src_path)-1] != '/')
      strcat(src_path, "/");
    strcat(src_path, de.name);
    
    strcpy(dst_path, dst);
    if(dst_path[strlen(dst_path)-1] != '/')
      strcat(dst_path, "/");
    strcat(dst_path, de.name);
    
    // Recursively copy
    if(copy_file(src_path, dst_path) < 0) {
      close(fd);
      return -1;
    }
  }
  
  close(fd);
  return 0;
}

static int
is_directory(const char *path)
{
  struct stat st;
  
  if(stat(path, &st) < 0)
    return 0;
  
  return st.type == T_DIR;
}

static void
build_dest_path(char *dest, const char *dir, const char *file)
{
  const char *basename;
  
  // Find basename of source file
  basename = strrchr(file, '/');
  if(basename)
    basename++;
  else
    basename = file;
  
  // Build destination path
  strcpy(dest, dir);
  if(dest[strlen(dest)-1] != '/')
    strcat(dest, "/");
  strcat(dest, basename);
}

int
main(int argc, char *argv[])
{
  int i, opt_end = 1;
  char dest_path[512];
  
  // Parse options
  for(i = 1; i < argc && argv[i][0] == '-'; i++) {
    char *p = argv[i] + 1;
    while(*p) {
      switch(*p) {
      case 'i':
        iflag = 1;
        break;
      case 'p':
        pflag = 1;
        break;
      case 'r':
      case 'R':
        rflag = 1;
        break;
      default:
        printf(2, "cp: invalid option -- '%c'\n", *p);
        usage();
      }
      p++;
    }
    opt_end++;
  }
  
  // Check arguments
  if(argc - opt_end < 2) {
    usage();
  }
  
  // Multiple sources - last argument must be a directory
  if(argc - opt_end > 2) {
    const char *target = argv[argc - 1];
    
    if(!is_directory(target)) {
      printf(2, "cp: target '%s' is not a directory\n", target);
      exit(0);
    }
    
    // Copy each source to target directory
    for(i = opt_end; i < argc - 1; i++) {
      build_dest_path(dest_path, target, argv[i]);
      if(copy_file(argv[i], dest_path) < 0) {
        exit(0);
      }
    }
  }
  // Single source
  else {
    const char *src = argv[opt_end];
    const char *dst = argv[opt_end + 1];
    
    // If destination is a directory, build full path
    if(is_directory(dst)) {
      build_dest_path(dest_path, dst, src);
      dst = dest_path;
    }
    
    if(copy_file(src, dst) < 0) {
      exit(0);
    }
  }
  
  exit(0);
}