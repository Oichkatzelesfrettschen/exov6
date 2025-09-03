#include "caplib.h"
#include "libos/driver.h"
#include "user.h"
#include "string.h"

// Simple character device driver demo
// This driver will expose a simple buffer that can be written to and read from.
// It will communicate via a Cap'n Proto service (conceptual).

#define DRIVER_BUFFER_SIZE 256
static char driver_buffer[DRIVER_BUFFER_SIZE];
static size_t current_pos = 0;

// Conceptual Cap'n Proto service for the character device
// In a real scenario, this would be generated from a .capnp schema
// and handle RPC requests.

// Function to handle write requests (conceptual)
int handle_write_request(const char *data, size_t len) {
    if (len > DRIVER_BUFFER_SIZE - current_pos) {
        len = DRIVER_BUFFER_SIZE - current_pos;
    }
    memcpy(driver_buffer + current_pos, data, len);
    current_pos += len;
    cprintf("CharDriver: Wrote %d bytes. Current pos: %d\n", (int)len, (int)current_pos);
    return (int)len;
}

// Function to handle read requests (conceptual)
int handle_read_request(char *data, size_t len) {
    if (len > current_pos) {
        len = current_pos;
    }
    memcpy(data, driver_buffer, len);
    cprintf("CharDriver: Read %d bytes. Current pos: %d\n", (int)len, (int)current_pos);
    return (int)len;
}

int main(void) {
    cprintf("\n--- Character Device Driver Demo ---\n");
    cprintf("CharDriver: Starting up...\n");

    // In a real driver, we would register a Cap'n Proto service
    // and listen for incoming requests from clients.
    // For this demo, we'll simulate some operations.

    // Simulate a write operation
    handle_write_request("Hello from CharDriver!", strlen("Hello from CharDriver!"));

    // Simulate a read operation
    char read_buf[DRIVER_BUFFER_SIZE];
    memset(read_buf, 0, sizeof(read_buf));
    int bytes_read = handle_read_request(read_buf, sizeof(read_buf));
    if (bytes_read > 0) {
        cprintf("CharDriver: Content: \"%s\"\n", read_buf);
    }

    cprintf("CharDriver: Demo complete. Driver would now enter a service loop.\n");

    // A real driver would typically enter an infinite loop here,
    // waiting for and processing requests.
    // while(1) { /* process requests */ }

    return 0;
}
