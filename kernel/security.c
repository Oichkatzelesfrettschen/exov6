#include <types.h>
#include <defs.h>
#include <param.h>
#include <memlayout.h>
#include <exov6_interface.h>

// The Lattice Rule: Bell-LaPadula "Simple Security Property"
// Read Down is OK. Write Up is OK.
// But Flow (Information transfer) checks are subtle.
// Here we check: Can info flow from SRC -> DEST?
int
can_flow(label_t src_label, label_t dest_label)
{
    // If Source is HIGH (1) and Dest is LOW (0), flow is FORBIDDEN.
    if (src_label > dest_label) {
        return 0;
    }
    return 1;
}
