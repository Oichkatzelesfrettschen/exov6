#pragma once

#ifndef __has_attribute
# define __has_attribute(x) 0
#endif

#ifndef __has_include
# define __has_include(x) 0
#endif

#define EXO_HAS_ATTR(x) __has_attribute(x)
