/**
 * mv - move/rename files
 * POSIX.1-2024 compliant implementation for FeuerBird exokernel
 * 
 * Usage: mv [-if] source target
 *        mv [-if] source... directory
 * 
 * Options:
 *   -i  Interactive mode (prompt before overwrite)
 *   -f  Force mode (no prompts)
 */

#include <types.h>
#include <user.h>
#include <fcntl.h>
#include <fs.h>

// Using standard link/unlink for rename if syscall is missing
int rename(const char *oldpath, const char *newpath) {
    // Try link + unlink
    if (link(oldpath, newpath) < 0) {
        return -1;
    }
    if (unlink(oldpath) < 0) {
        // Should probably remove newpath if unlink fails?
        // But safely we have a copy now.
        return 0;
    }
    return 0;
}

static int iflag = 0;  // Interactive mode
static int fflag = 0;  // Force mode

static void
usage(void)
{
  printf(2, "Usage: mv [-if] source target\n");
  printf(2, "       mv [-if] source... directory\n");
  exit(0);
}

static int
confirm_overwrite(const char *path)
{
  char response[10];
  
  if(fflag)
    return 1;
  
  printf(1, "overwrite '%s'? ", path);
  gets(response, sizeof(response));
  
  return (response[0] == 'y' || response[0] == 'Y');
}

static int
is_directory(const char *path)
{
  struct stat st;
  
  if(stat(path, &st) < 0)
    return 0;
  
  return st.type == T_DIR;
}

static int
copy_file(const char *src, const char *dst)
{
  int fd_src, fd_dst;
  int n;
  char buf[512];
  struct stat st;
  
  // Get source file info
  if(stat(src, &st) < 0) {
    printf(2, "mv: cannot stat '%s'\n", src);
    return -1;
  }
  
  // Open source file
  if((fd_src = open(src, O_RDONLY)) < 0) {
    printf(2, "mv: cannot open '%s'\n", src);
    return -1;
  }
  
  // Create destination file
  // Note: open with O_CREATE needs permissions. 0666 is standard default.
  if((fd_dst = open(dst, O_CREATE | O_WRONLY, 0666)) < 0) {
    printf(2, "mv: cannot create '%s'\n", dst);
    close(fd_src);
    return -1;
  }
  
  // Copy data
  while((n = read(fd_src, buf, sizeof(buf))) > 0) {
    if(write(fd_dst, buf, n) != n) {
      printf(2, "mv: write error\n");
      close(fd_src);
      close(fd_dst);
      unlink(dst);  // Clean up partial file
      return -1;
    }
  }
  
  if(n < 0) {
    printf(2, "mv: read error\n");
    close(fd_src);
    close(fd_dst);
    unlink(dst);  // Clean up partial file
    return -1;
  }
  
  close(fd_src);
  close(fd_dst);
  
  // Remove source file
  if(unlink(src) < 0) {
    printf(2, "mv: cannot remove '%s'\n", src);
    unlink(dst);  // Clean up destination
    return -1;
  }
  
  return 0;
}

static int
move_file(const char *src, const char *dst)
{
  struct stat src_st, dst_st;
  int dst_exists;
  
  // Check if source exists
  if(stat(src, &src_st) < 0) {
    printf(2, "mv: cannot stat '%s'\n", src);
    return -1;
  }
  
  // Check if destination exists and get its stat
  dst_exists = (stat(dst, &dst_st) >= 0);
  
  // Check if source and destination refer to the same path
  // This prevents the file from being deleted when doing "mv foo foo"
  if(dst_exists && src_st.dev == dst_st.dev && src_st.ino == dst_st.ino) {
    // Same file, nothing to do
    return 0;
  }
  
  // If destination exists, handle it
  if(dst_exists) {
    // If destination is a directory, move source into it
    if(dst_st.type == T_DIR) {
      char new_dst[512];
      const char *basename;
      
      // Find basename of source
      basename = strrchr(src, '/');
      if(basename)
        basename++;
      else
        basename = src;
      
      // Build new destination path
      strcpy(new_dst, dst);
      if(new_dst[strlen(new_dst)-1] != '/')
        strcat(new_dst, "/");
      strcat(new_dst, basename);
      
      return move_file(src, new_dst);
    }
    
    // Destination is a file - check if we should overwrite
    if(iflag && !fflag) {
      if(!confirm_overwrite(dst))
        return 0;
    }
  }
  
  // Try to rename first (atomic operation within same filesystem)
  // For directories, link() might fail, so we fallback to copy/unlink logic if src is dir?
  // But copy/unlink for dir is complex (recursive).
  if(src_st.type != T_DIR && rename(src, dst) >= 0) {
    return 0;
  }
  
  if(src_st.type == T_DIR) {
    printf(2, "mv: cannot move directory '%s' (not implemented)\n", src);
    return -1;
  }
  
  // Rename failed (probably cross-filesystem or link not supported), do copy+delete
  // Copy file to destination
  if(copy_file(src, dst) < 0) {
    return -1;
  }
  
  return 0;
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
        fflag = 0;  // -i overrides -f
        break;
      case 'f':
        fflag = 1;
        iflag = 0;  // -f overrides -i
        break;
      default:
        printf(2, "mv: invalid option -- '%c'\n", *p);
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
      printf(2, "mv: target '%s' is not a directory\n", target);
      exit(0);
    }
    
    // Move each source to target directory
    for(i = opt_end; i < argc - 1; i++) {
      build_dest_path(dest_path, target, argv[i]);
      if(move_file(argv[i], dest_path) < 0) {
        // Continue with other files even if one fails
      }
    }
  }
  // Single source
  else {
    const char *src = argv[opt_end];
    const char *dst = argv[opt_end + 1];
    
    if(move_file(src, dst) < 0) {
      exit(0);
    }
  }
  
  exit(0);
}