#include <stdio.h>
#include <stdlib.h>
#include <time.h>

#define NBAT 3
#define NROOM 20
#define NTUNN 3
#define NPIT 3

struct room { int tunn[NTUNN]; int flag; };

static struct room rooms[NROOM];

static const char *intro[] = {
    "\n",
    "Welcome to 'Hunt the Wumpus.'\n",
    "\n",
    "The Wumpus lives in a cave of %d rooms.\n",
    "Each room has %d tunnels leading to other rooms.\n",
    "\n",
    NULL
};

#define BAT  01
#define PIT  02
#define WUMP 04

static int arrow;
static int loc;
static int wloc;
static int tchar;

static int rnum(int n) {
    return rand() % n;
}

static int rline(void) {
    int c; while ((c=getchar())==' ');
    int r=c; while(c!='\n' && c!=' ') { if(c==EOF) exit(0); c=getchar(); }
    tchar=c; return r;
}

static int rin(void) {
    int n=0,c=getchar();
    while(c!='\n' && c!=' ') { if(c<'0'||c>'9') { while(c!='\n'&&c!=EOF) c=getchar(); return 0; } n=n*10+c-'0'; c=getchar(); }
    return n;
}

static int near(struct room *p, int haz) {
    for(int i=0;i<NTUNN;i++) if(rooms[p->tunn[i]].flag & haz) return 1; return 0;
}

static int icomp(const void*a,const void*b){return *(int*)a-*(int*)b;}

static int tunnel(int i){int n,j,c=20;while(1){n=rnum(NROOM);if(n==i){if(--c>0)continue;}struct room*p=&rooms[n];for(j=0;j<NTUNN;j++)if(p->tunn[j]==-1){p->tunn[j]=i;return n;}}}

int main(void){srand(time(NULL));printf("Instructions? (y-n) ");if(rline()=='y')for(int i=0;intro[i];i++)printf(intro[i],i&1?NROOM:NTUNN);
init:;
for(int i=0;i<NROOM;i++){for(int j=0;j<NTUNN;j++)rooms[i].tunn[j]=-1;rooms[i].flag=0;}
int k=0;for(int i=1;i<NROOM;){int j=rnum(NROOM);struct room*p=&rooms[j];if(j==k||p->tunn[0]>=0||p->tunn[1]>=0)continue;p->tunn[1]=k;rooms[k].tunn[0]=j;k=j;i++;}
for(int i=0;i<NROOM;i++){struct room*p=&rooms[i];for(int j=0;j<NTUNN;j++){if(p->tunn[j]<0)p->tunn[j]=tunnel(i);if(p->tunn[j]==i)goto init;for(int x=0;x<j;x++)if(p->tunn[j]==p->tunn[x])goto init;}qsort(p->tunn,NTUNN,sizeof(int),icomp);} 
setup:;
arrow=5;for(int i=0;i<NROOM;i++)rooms[i].flag=0;for(int i=0;i<NPIT;){struct room*p=&rooms[rnum(NROOM)];if(!(p->flag&PIT)){p->flag|=PIT;i++;}}
for(int i=0;i<NBAT;){struct room*p=&rooms[rnum(NROOM)];if(!(p->flag&(PIT|BAT))){p->flag|=BAT;i++;}}
int i=rnum(NROOM);wloc=i;rooms[i].flag|=WUMP;while(1){i=rnum(NROOM);if(!(rooms[i].flag&(PIT|BAT|WUMP))){loc=i;break;}}
loop:;
printf("You are in room %d\n",loc+1);struct room*p=&rooms[loc];if(p->flag&PIT){printf("You fell into a pit\n");goto done;}if(p->flag&WUMP){printf("You were eaten by the wumpus\n");goto done;}if(p->flag&BAT){printf("Theres a bat in your room\n");loc=rnum(NROOM);goto loop;}for(int i=0;i<NTUNN;i++)if(near(&rooms[p->tunn[i]],WUMP))goto nearwump;if(near(p,WUMP)){nearwump:printf("I smell a wumpus\n");}if(near(p,BAT))printf("Bats nearby\n");if(near(p,PIT))printf("I feel a draft\n");printf("There are tunnels to");for(int i=0;i<NTUNN;i++)printf(" %d",p->tunn[i]+1);printf("\n");
again:printf("Move or shoot (m-s) ");switch(rline()){case 'm':if(tchar=='\n')printf("which room? ");i=rin()-1;for(int j=0;j<NTUNN;j++)if(i==p->tunn[j])goto groom;printf("You hit the wall\n");goto again;groom:loc=i;if(i==wloc)goto mwump;goto loop;case 's':if(tchar=='\n')printf("Give list of rooms terminated by 0\n");for(i=0;i<5;i++){int j=rin()-1;if(j==-1)break;ranarw:for(k=0;k<NTUNN;k++)if(j==p->tunn[k])goto garow;j=rnum(NROOM);goto ranarw;garow:p=&rooms[j];if(j==loc){printf("You shot yourself\n");goto done;}if(p->flag&WUMP){printf("You slew the wumpus\n");goto done;}}if(--arrow==0){printf("That was your last shot\n");goto done;}goto mwump;}goto again;
mwump:p=&rooms[wloc];p->flag&=~WUMP;i=rnum(NTUNN+1);if(i!=NTUNN)wloc=p->tunn[i];rooms[wloc].flag|=WUMP;goto loop;
done:printf("Another game? (y-n) ");if(rline()=='y'){printf("Same room setup? (y-n) ");if(rline()=='y')goto setup;goto init;}return 0;}
