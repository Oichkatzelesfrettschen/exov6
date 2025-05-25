#include "exo_stream.h"
#include "streams.h"

void streams_stop(void) { exo_stream_halt(); }

void streams_yield(void) { exo_stream_yield(); }
