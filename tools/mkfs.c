#include <stdio.h>
#include <unistd.h>
#include <stdlib.h>
#include <string.h>
#include <fcntl.h>
#include <assert.h>
#include <stdint.h>
#include <sys/stat.h>

// Avoid including kernel headers - define what we need locally
#define BSIZE 512
#define NDIRECT 12
#define NINDIRECT (BSIZE / sizeof(uint32_t))
#define MAXFILE (NDIRECT + NINDIRECT)
#define ROOTINO 1
#define FSSIZE 1000
#define LOGSIZE 30
#define IPB (BSIZE / sizeof(struct dinode))
#define BPB (BSIZE * 8)

// File types
#define T_DIR  1
#define T_FILE 2
#define T_DEV  3

// Filesystem structures
struct superblock {
    uint32_t size;
    uint32_t nblocks;
    uint32_t ninodes;
    uint32_t nlog;
    uint32_t logstart;
    uint32_t inodestart;
    uint32_t bmapstart;
};

struct dinode {
    short type;
    short major;
    short minor;
    short nlink;
    uint32_t size;
    uint32_t addrs[NDIRECT + 1];
};

struct dirent {
    uint16_t inum;
    char name[14];
};

#define IBLOCK(i, sb) ((i) / IPB + sb.inodestart)
#define BBLOCK(b, sb) (b/BPB + sb.bmapstart)
#define GU_MIN(a, b) ((a) < (b) ? (a) : (b))

#ifndef static_assert
#define static_assert(a, b) do { switch (0) case 0: case (a): ; } while (0)
#endif

#define NINODES 200

// Disk layout:
// [ boot block | sb block | log | inode blocks | free bit map | data blocks ]

int nbitmap = FSSIZE/(BSIZE*8) + 1;
int ninodeblocks = NINODES / IPB + 1;
int nlog = LOGSIZE;
int nmeta;    // Number of meta blocks (boot, sb, nlog, inode, bitmap)
int nblocks;  // Number of data blocks

int fsfd;
struct superblock sb;
char zeroes[BSIZE];
uint32_t freeinode = 1;
uint32_t freeblock;


void balloc(int);
void wsect(uint32_t, void*);
void winode(uint32_t, struct dinode*);
void rinode(uint32_t inum, struct dinode *ip);
void rsect(uint32_t sec, void *buf);
uint32_t ialloc(uint16_t type);
void iappend(uint32_t inum, void *p, int n);

// convert to intel byte order
uint16_t
xshort(uint16_t x)
{
  uint16_t y;
  uint8_t *a = (uint8_t*)&y;
  a[0] = x;
  a[1] = x >> 8;
  return y;
}

uint32_t
xint(uint32_t x)
{
  uint32_t y;
  uint8_t *a = (uint8_t*)&y;
  a[0] = x;
  a[1] = x >> 8;
  a[2] = x >> 16;
  a[3] = x >> 24;
  return y;
}

int
main(int argc, char *argv[])
{
  int i, cc, fd;
  uint32_t rootino, inum, off;
  struct dirent de;
  char buf[BSIZE];
  struct dinode din;


  static_assert(sizeof(int) == 4, "Integers must be 4 bytes!");

  if(argc < 2){
    fprintf(stderr, "Usage: mkfs fs.img files...\n");
    exit(1);
  }

  assert((BSIZE % sizeof(struct dinode)) == 0);
  assert((BSIZE % sizeof(struct dirent)) == 0);

  fsfd = open(argv[1], O_RDWR|O_CREAT|O_TRUNC, 0666);
  if(fsfd < 0){
    perror(argv[1]);
    exit(1);
  }

  // 1 fs block = 1 disk sector
  nmeta = 2 + nlog + ninodeblocks + nbitmap;
  nblocks = FSSIZE - nmeta;

  sb.size = FSSIZE;
  sb.nblocks = nblocks;
  sb.ninodes = NINODES;
  sb.nlog = nlog;
  sb.logstart = 2;
  sb.inodestart = 2+nlog;
  sb.bmapstart = 2+nlog+ninodeblocks;

  printf("nmeta %d (boot, super, log blocks %u inode blocks %u, bitmap blocks %u) blocks %d total %d\n",
         nmeta, nlog, ninodeblocks, nbitmap, nblocks, FSSIZE);

  freeblock = nmeta;     // the first free block that we can allocate

  for(i = 0; i < FSSIZE; i++)
    wsect(i, zeroes);

  memset(buf, 0, sizeof(buf));
  memmove(buf, &sb, sizeof(sb));
  wsect(1, buf);

  rootino = ialloc(T_DIR);
  assert(rootino == ROOTINO);

  memset(&de, 0, sizeof(de));
  de.inum = rootino;
  strncpy(de.name, ".", sizeof(de.name));
  iappend(rootino, &de, sizeof(de));

  memset(&de, 0, sizeof(de));
  de.inum = rootino;
  strncpy(de.name, "..", sizeof(de.name));
  iappend(rootino, &de, sizeof(de));

  for(i = 2; i < argc; i++){
    // Get basename of file
    char *fname = strrchr(argv[i], '/');
    if (fname)
      fname++;
    else
      fname = argv[i];
    assert(strlen(fname) < sizeof(de.name));

    if((fd = open(argv[i], 0)) < 0){
      perror(argv[i]);
      exit(1);
    }

    // Skip leading _ in name when writing to file system.
    // The binaries are named _rm, _cat, etc. to keep the
    // build operating system from trying to execute them
    // in place of system binaries like rm and cat.
    if(argv[i][0] == '_')
      ++argv[i];

    inum = ialloc(T_FILE);

    memset(&de, 0, sizeof(de));
    de.inum = inum;
    strncpy(de.name, fname, sizeof(de.name) - 1);
    iappend(rootino, &de, sizeof(de));

    while((cc = read(fd, buf, sizeof(buf))) > 0)
      iappend(inum, buf, cc);

    close(fd);
  }

  // fix size of root inode dir
  rinode(rootino, &din);
  off = xint(din.size);
  off = ((off/BSIZE) + 1) * BSIZE;
  din.size = xint(off);
  winode(rootino, &din);

  balloc(freeblock);

  exit(0);
}

void
wsect(uint32_t sec, void *buf)
{
  if(lseek(fsfd, sec * BSIZE, 0) != sec * BSIZE){
    perror("lseek");
    exit(1);
  }
  if(write(fsfd, buf, BSIZE) != BSIZE){
    perror("write");
    exit(1);
  }
}

void
winode(uint32_t inum, struct dinode *ip)
{
  char buf[BSIZE];
  uint32_t bn;
  struct dinode *dip;

  bn = IBLOCK(inum, sb);
  rsect(bn, buf);
  dip = ((struct dinode*)buf) + (inum % IPB);
  *dip = *ip;
  wsect(bn, buf);
}

void
rinode(uint32_t inum, struct dinode *ip)
{
  char buf[BSIZE];
  uint32_t bn;
  struct dinode *dip;

  bn = IBLOCK(inum, sb);
  rsect(bn, buf);
  dip = ((struct dinode*)buf) + (inum % IPB);
  *ip = *dip;
}

void
rsect(uint32_t sec, void *buf)
{
  if(lseek(fsfd, sec * BSIZE, 0) != sec * BSIZE){
    perror("lseek");
    exit(1);
  }
  if(read(fsfd, buf, BSIZE) != BSIZE){
    perror("read");
    exit(1);
  }
}

uint32_t
ialloc(uint16_t type)
{
  uint32_t inum = freeinode++;
  struct dinode din;

  memset(&din, 0, sizeof(din));
  din.type = xshort(type);
  din.nlink = xshort(1);
  din.size = xint(0);
  winode(inum, &din);
  return inum;
}

void
balloc(int used)
{
  uint8_t buf[BSIZE];
  int i;

  printf("balloc: first %d blocks have been allocated\n", used);
  assert(used < BSIZE*8);
  memset(buf, 0, BSIZE);
  for(i = 0; i < used; i++){
    buf[i/8] = buf[i/8] | (0x1 << (i%8));
  }
  printf("balloc: write bitmap block at sector %u\n", sb.bmapstart);
  wsect(sb.bmapstart, buf);
}


void
iappend(uint32_t inum, void *xp, int n)
{
  char *p = (char*)xp;
  uint32_t fbn, off, n1;
  struct dinode din;
  char buf[BSIZE];
  uint32_t indirect[NINDIRECT];
  uint32_t x;

  rinode(inum, &din);
  off = xint(din.size);
  // printf("append inum %d at off %d sz %d\n", inum, off, n);
  while(n > 0){
    fbn = off / BSIZE;
    assert(fbn < MAXFILE);
    if(fbn < NDIRECT){
      if(xint(din.addrs[fbn]) == 0){
        din.addrs[fbn] = xint(freeblock++);
      }
      x = xint(din.addrs[fbn]);
    } else {
      if(xint(din.addrs[NDIRECT]) == 0){
        din.addrs[NDIRECT] = xint(freeblock++);
      }
      rsect(xint(din.addrs[NDIRECT]), (char*)indirect);
      if(indirect[fbn - NDIRECT] == 0){
        indirect[fbn - NDIRECT] = xint(freeblock++);
        wsect(xint(din.addrs[NDIRECT]), (char*)indirect);
      }
      x = xint(indirect[fbn-NDIRECT]);
    }
    n1 = GU_MIN(n, (fbn + 1) * BSIZE - off);
    rsect(x, buf);
    memcpy(p, buf + off - (fbn * BSIZE), n1);
    wsect(x, buf);
    n -= n1;
    off += n1;
    p += n1;
  }
  din.size = xint(off);
  winode(inum, &din);
}
