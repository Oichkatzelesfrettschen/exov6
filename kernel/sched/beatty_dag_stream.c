#include <types.h>
#include "defs.h"
#include "exo_stream.h"

/* Forward declarations */
extern struct exo_sched_ops *beatty_sched_ops(void);
extern struct exo_sched_ops *dag_sched_ops(void);

/* Initialize the combined Beatty+DAG stream. Call once during boot
 * after both schedulers are registered so Beatty can select which DAG
 * family runs next. */
void
beatty_dag_stream_init(void)
{
    struct exo_sched_ops *bops = beatty_sched_ops();
    struct exo_sched_ops *dops = dag_sched_ops();

    /* Chain the DAG scheduler under the Beatty scheduler and activate. */
    bops->next = dops;

    static struct exo_stream bs;
    bs.head = bops;
    exo_stream_register(&bs);
}
