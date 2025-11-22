#pragma once
struct qspinlock { int locked; };
#define qspin_init(l, n, f)
#define qspin_lock(l)
#define qspin_unlock(l)
