/* stdnoreturn.h - C11/C17 noreturn macro */
#ifndef _STDNORETURN_H
#define _STDNORETURN_H

#ifndef __cplusplus
#define noreturn _Noreturn
#endif

/* C23 deprecated this header but we keep it for C17 compatibility */
#define __noreturn_is_defined 1

#endif /* _STDNORETURN_H */
