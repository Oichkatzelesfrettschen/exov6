#include "chan.h"
#include "user.h"
#include "caplib.h"

/**
 * Implementation of unified channel functions
 * 
 * Note: Basic channel functions are provided as inline compatibility
 * wrappers in chan.h. This file contains implementations for the
 * unified channel system when needed.
 *
 * All core channel functions (chan_create, chan_destroy, chan_endpoint_send,
 * chan_endpoint_recv) are now provided as inline wrappers that delegate
 * to the unified channel system.
 */
