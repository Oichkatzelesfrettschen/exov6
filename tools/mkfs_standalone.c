// Standalone mkfs for ExoKernel v6
// Builds filesystem image without header conflicts

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <fcntl.h>
#include <unistd.h>
#include <assert.h>

#define BSIZE 512
#define FSSIZE 1000
#define MAXFILE 100
#define NDIRECT 12
#define NINDIRECT (BSIZE / sizeof(uint))
#define MAXOPBLOCKS 10
#define LOGSIZE (MAXOPBLOCKS*3)
#define NBUF (MAXOPBLOCKS*3)
#define NINODES 200
#define ROOTINO 1
#define DIRSIZ 14

typedef unsigned int uint;
typedef unsigned short ushort;
typedef unsigned char uchar;

// File system structures
struct superblock {
    uint size;
    uint nblocks;
    uint ninodes;
    uint nlog;
    uint logstart;
    uint inodestart;
    uint bmapstart;
};

struct dinode {
    short type;
    short major;
    short minor;
    short nlink;
    uint size;
    uint addrs[NDIRECT+1];
};

struct dirent {
    ushort inum;
    char name[DIRSIZ];
};

#define T_DIR  1
#define T_FILE 2
#define T_DEV  3

#define IPB (BSIZE / sizeof(struct dinode))
#define IBLOCK(i, sb) ((i) / IPB + (sb).inodestart)
#define BPB (BSIZE*8)
#define BBLOCK(b, sb) ((b)/BPB + (sb).bmapstart)

int fsfd;
struct superblock sb;
char zeroes[BSIZE];
uint freeblock;
uint usedblocks;
uint bitblocks;
uint freeinode = 1;

void balloc(int);
void wsect(uint, void*);
void winode(uint, struct dinode*);
void rinode(uint inum, struct dinode *ip);
void rsect(uint sec, void *buf);
uint ialloc(ushort type);
void iappend(uint inum, void *p, int n);

int main(int argc, char *argv[]) {
    int i, cc, fd;
    uint rootino, inum, off;
    struct dirent de;
    struct dinode din;
    char buf[BSIZE];

    if(argc < 2) {
        fprintf(stderr, "Usage: mkfs fs.img files...\n");
        exit(1);
    }

    assert((BSIZE % sizeof(struct dinode)) == 0);
    assert((BSIZE % sizeof(struct dirent)) == 0);

    fsfd = open(argv[1], O_RDWR|O_CREAT|O_TRUNC, 0666);
    if(fsfd < 0) {
        perror(argv[1]);
        exit(1);
    }

    // Build superblock
    sb.size = FSSIZE;
    sb.nblocks = FSSIZE;
    sb.ninodes = NINODES;
    sb.nlog = LOGSIZE;
    sb.logstart = 2;
    sb.inodestart = 2 + LOGSIZE;
    sb.bmapstart = 2 + LOGSIZE + NINODES / IPB + 1;

    bitblocks = FSSIZE/(BSIZE*8) + 1;
    usedblocks = sb.bmapstart + bitblocks;
    freeblock = usedblocks;

    printf("mkfs: building filesystem image %s\n", argv[1]);
    printf("  blocks: %d\n", FSSIZE);
    printf("  inodes: %d\n", NINODES);
    printf("  log blocks: %d\n", LOGSIZE);
    
    // Clear everything
    for(i = 0; i < FSSIZE; i++)
        wsect(i, zeroes);

    // Write superblock
    memset(buf, 0, sizeof(buf));
    memmove(buf, &sb, sizeof(sb));
    wsect(1, buf);

    // Allocate root inode
    rootino = ialloc(T_DIR);
    assert(rootino == ROOTINO);

    // Add . and .. entries to root
    memset(&de, 0, sizeof(de));
    de.inum = rootino;
    strcpy(de.name, ".");
    iappend(rootino, &de, sizeof(de));

    memset(&de, 0, sizeof(de));
    de.inum = rootino;
    strcpy(de.name, "..");
    iappend(rootino, &de, sizeof(de));

    // Add files from command line
    for(i = 2; i < argc; i++) {
        char *shortname;
        
        if((fd = open(argv[i], 0)) < 0) {
            fprintf(stderr, "mkfs: cannot open %s\n", argv[i]);
            continue;
        }

        // Skip leading path
        if((shortname = strrchr(argv[i], '/')))
            shortname++;
        else
            shortname = argv[i];

        // Skip underscore prefix
        if(*shortname == '_')
            shortname++;

        // Truncate to DIRSIZ
        if(strlen(shortname) >= DIRSIZ)
            shortname[DIRSIZ-1] = '\0';

        inum = ialloc(T_FILE);

        memset(&de, 0, sizeof(de));
        de.inum = inum;
        strncpy(de.name, shortname, DIRSIZ);
        iappend(rootino, &de, sizeof(de));

        while((cc = read(fd, buf, sizeof(buf))) > 0)
            iappend(inum, buf, cc);

        close(fd);
    }

    // Fix size of root inode dir
    rinode(rootino, &din);
    off = din.size;
    off = ((off/BSIZE) + 1) * BSIZE;
    din.size = off;
    winode(rootino, &din);

    balloc(freeblock);

    printf("mkfs: created %s with %d files\n", argv[1], argc-2);
    exit(0);
}

void wsect(uint sec, void *buf) {
    if(lseek(fsfd, sec * BSIZE, 0) != sec * BSIZE) {
        perror("lseek");
        exit(1);
    }
    if(write(fsfd, buf, BSIZE) != BSIZE) {
        perror("write");
        exit(1);
    }
}

void winode(uint inum, struct dinode *ip) {
    char buf[BSIZE];
    uint bn;
    struct dinode *dip;

    bn = IBLOCK(inum, sb);
    rsect(bn, buf);
    dip = ((struct dinode*)buf) + (inum % IPB);
    *dip = *ip;
    wsect(bn, buf);
}

void rinode(uint inum, struct dinode *ip) {
    char buf[BSIZE];
    uint bn;
    struct dinode *dip;

    bn = IBLOCK(inum, sb);
    rsect(bn, buf);
    dip = ((struct dinode*)buf) + (inum % IPB);
    *ip = *dip;
}

void rsect(uint sec, void *buf) {
    if(lseek(fsfd, sec * BSIZE, 0) != sec * BSIZE) {
        perror("lseek");
        exit(1);
    }
    if(read(fsfd, buf, BSIZE) != BSIZE) {
        perror("read");
        exit(1);
    }
}

uint ialloc(ushort type) {
    uint inum = freeinode++;
    struct dinode din;

    memset(&din, 0, sizeof(din));
    din.type = type;
    din.nlink = 1;
    din.size = 0;
    winode(inum, &din);
    return inum;
}

void balloc(int used) {
    uchar buf[BSIZE];
    int i;

    for(i = 0; i < used; i += BPB) {
        memset(buf, 0xff, BSIZE);
        wsect(sb.bmapstart + i/BPB, buf);
    }
}

void iappend(uint inum, void *xp, int n) {
    char *p = (char*)xp;
    uint fbn, off, n1;
    struct dinode din;
    char buf[BSIZE];
    uint indirect[NINDIRECT];
    uint x;

    rinode(inum, &din);
    off = din.size;
    
    while(n > 0) {
        fbn = off / BSIZE;
        assert(fbn < MAXFILE);
        
        if(fbn < NDIRECT) {
            if(din.addrs[fbn] == 0) {
                din.addrs[fbn] = freeblock++;
            }
            x = din.addrs[fbn];
        } else {
            if(din.addrs[NDIRECT] == 0) {
                din.addrs[NDIRECT] = freeblock++;
            }
            rsect(din.addrs[NDIRECT], (char*)indirect);
            if(indirect[fbn - NDIRECT] == 0) {
                indirect[fbn - NDIRECT] = freeblock++;
                wsect(din.addrs[NDIRECT], (char*)indirect);
            }
            x = indirect[fbn - NDIRECT];
        }
        
        n1 = BSIZE - (off % BSIZE);
        if(n1 > n)
            n1 = n;
        rsect(x, buf);
        memmove(p, buf + (off % BSIZE), n1);
        wsect(x, buf);
        n -= n1;
        off += n1;
        p += n1;
    }
    
    din.size = off;
    winode(inum, &din);
}