#pragma once
struct sleeplock { int locked; };
void initsleeplock(struct sleeplock *lk, const char *name, int level);
void acquiresleep(struct sleeplock *lk);
void releasesleep(struct sleeplock *lk);
