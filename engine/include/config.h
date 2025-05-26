#pragma once

#include <compiler_attrs.h>

/* Optional local configuration overrides. */
#if __has_include(<config_local.h>)
# include <config_local.h>
#endif

#ifndef CONFIG_SMP
#define CONFIG_SMP 1
#endif
