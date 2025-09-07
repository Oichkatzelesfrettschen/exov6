#ifndef EXO_CAP_H
#define EXO_CAP_H

/* pick up the real declarations of:
 *   int cap_alloc_page(void);
 *   int cap_unbind_page(int cap_id, void *vaddr);
 *   int cap_bind_page(int cap_id, void *vaddr, int rights);
 *   int cap_inc(int cap_id);
 *   int cap_revoke(int cap_id);
 *   int cap_refcount(int cap_id, int *out_count);
 */
#include "../include/exokernel.h"

#ifdef __cplusplus
extern "C" {
#endif

/* exo_cap is already defined in exo.h (via exokernel.h) */

/* allocate a fresh page-cap */
exo_cap  mk_cap_alloc_page(void);

/* free/unbind the page associated with the cap */
int      mk_cap_free_page(exo_cap cap);

/* duplicate/increment a cap’s refcount and return the new cap in *out */
int      mk_cap_dup(exo_cap cap, exo_cap *out);

/* bind a page-cap into your address space at vaddr with given rights */
int      mk_cap_bind_page(exo_cap cap, void *vaddr, int rights);

/* unbind a page-cap from your address space at vaddr */
int      mk_cap_unbind_page(exo_cap cap, void *vaddr);

/* revoke (destroy) the cap entirely */
int      mk_cap_revoke(exo_cap cap);

/* query the current ref-count of a cap */
int      mk_cap_refcount(exo_cap cap, int *out_count);

#ifdef __cplusplus
}
#endif

#endif /* EXO_CAP_H */
