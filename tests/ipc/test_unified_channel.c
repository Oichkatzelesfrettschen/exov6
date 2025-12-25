/**
 * @file test_unified_channel.c
 * @brief Comprehensive test suite for unified channel system
 * 
 * Tests all aspects of the IPC system:
 * - Basic send/receive operations
 * - Serialization layers
 * - Capability validation
 * - Performance characteristics
 * - Error conditions
 * - Stress testing
 */

#include "../../include/ipc/unified_channel.h"
#include "../../include/ipc/serialization.h"
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <assert.h>
#include <time.h>
#include <unistd.h>

// =============================================================================
// TEST FRAMEWORK
// =============================================================================

static int tests_passed = 0;
static int tests_failed = 0;
static int tests_skipped = 0;

#define TEST_ASSERT(condition, message) do { \
    if (condition) { \
        printf("✓ %s\n", message); \
        tests_passed++; \
    } else { \
        printf("✗ %s\n", message); \
        tests_failed++; \
    } \
} while(0)

#define TEST_SKIP(message) do { \
    printf("⊘ %s (SKIPPED)\n", message); \
    tests_skipped++; \
} while(0)

#define RUN_TEST(test_func) do { \
    printf("\n=== Running %s ===\n", #test_func); \
    test_func(); \
} while(0)

// =============================================================================
// TEST MESSAGE TYPES
// =============================================================================

typedef struct {
    uint32_t id;
    uint64_t timestamp;
    char data[256];
} test_message_t;

typedef struct {
    int32_t x, y, z;
    float velocity;
    bool active;
} position_message_t;

typedef struct {
    uint8_t command;
    uint16_t params[8];
    uint32_t checksum;
} control_message_t;

// Define typed channels for testing
DEFINE_TYPED_CHANNEL(test, test_message_t);
DEFINE_TYPED_CHANNEL(position, position_message_t);
DEFINE_TYPED_CHANNEL(control, control_message_t);

// =============================================================================
// TEST UTILITIES
// =============================================================================

static test_message_t create_test_message(uint32_t id) {
    test_message_t msg = {0};
    msg.id = id;
    msg.timestamp = (uint64_t)time(NULL);
    snprintf(msg.data, sizeof(msg.data), "Test message %u", id);
    return msg;
}

static bool validate_test_message(const test_message_t* received, 
                                 const test_message_t* expected) {
    return received->id == expected->id &&
           strcmp(received->data, expected->data) == 0;
}

static exo_cap_t create_test_capability(uint64_t base_id, uint32_t permissions) {
    return (base_id << 16) | permissions;
}

// =============================================================================
// BASIC FUNCTIONALITY TESTS
// =============================================================================

void test_channel_creation_destruction(void) {
    channel_config_t config = {
        .type = CHAN_TYPE_SYNC,
        .mode = CHAN_MODE_BLOCKING,
        .buffer_size = 0,
        .message_size = sizeof(test_message_t),
        .max_receivers = 1,
        .timeout_ms = 1000,
        .serializer = SERIAL_RAW,
        .zero_copy = true,
        .ordered = true,
        .reliable = true
    };
    
    exo_cap_t owner_cap = create_test_capability(1, 0xFFFF);
    
    unified_channel_t* chan = channel_create("test_sync", &config, owner_cap);
    TEST_ASSERT(chan != NULL, "Sync channel creation");
    TEST_ASSERT(strcmp(chan->name, "test_sync") == 0, "Channel name correct");
    TEST_ASSERT(chan->config.type == CHAN_TYPE_SYNC, "Channel type correct");
    TEST_ASSERT(chan->serializer == &raw_serializer, "Raw serializer selected");
    
    int destroy_result = channel_destroy(chan);
    TEST_ASSERT(destroy_result == 0, "Channel destruction");
}

void test_async_channel_creation(void) {
    channel_config_t config = {
        .type = CHAN_TYPE_ASYNC,
        .mode = CHAN_MODE_NONBLOCKING,
        .buffer_size = 4096,
        .message_size = sizeof(test_message_t),
        .max_receivers = 1,
        .timeout_ms = 0,
        .serializer = SERIAL_CAPNP_LITE,
        .zero_copy = false,
        .ordered = true,
        .reliable = true
    };
    
    exo_cap_t owner_cap = create_test_capability(2, 0xFFFF);
    
    unified_channel_t* chan = channel_create("test_async", &config, owner_cap);
    TEST_ASSERT(chan != NULL, "Async channel creation");
    TEST_ASSERT(chan->buffer != NULL, "Async channel buffer allocated");
    TEST_ASSERT(chan->serializer == &capnp_lite_serializer, "Cap'n Proto Lite serializer selected");
    TEST_ASSERT(channel_is_empty(chan), "New async channel is empty");
    TEST_ASSERT(!channel_is_full(chan), "New async channel is not full");
    TEST_ASSERT(channel_pending_count(chan) == 0, "New async channel has zero pending");
    
    channel_destroy(chan);
}

void test_serializer_selection(void) {
    channel_config_t raw_config = {
        .type = CHAN_TYPE_SYNC,
        .serializer = SERIAL_RAW,
        .message_size = sizeof(test_message_t)
    };
    
    channel_config_t lite_config = {
        .type = CHAN_TYPE_ASYNC,
        .serializer = SERIAL_CAPNP_LITE,
        .buffer_size = 1024,
        .message_size = sizeof(test_message_t)
    };
    
    channel_config_t full_config = {
        .type = CHAN_TYPE_SYNC,
        .serializer = SERIAL_CAPNP_FULL,
        .message_size = sizeof(test_message_t)
    };
    
    exo_cap_t owner_cap = create_test_capability(3, 0xFFFF);
    
    unified_channel_t* raw_chan = channel_create("raw", &raw_config, owner_cap);
    unified_channel_t* lite_chan = channel_create("lite", &lite_config, owner_cap);
    unified_channel_t* full_chan = channel_create("full", &full_config, owner_cap);
    
    TEST_ASSERT(raw_chan->serializer == &raw_serializer, "Raw serializer selection");
    TEST_ASSERT(lite_chan->serializer == &capnp_lite_serializer, "Lite serializer selection");
    TEST_ASSERT(full_chan->serializer == &capnp_full_serializer, "Full serializer selection");
    
    channel_destroy(raw_chan);
    channel_destroy(lite_chan);
    channel_destroy(full_chan);
}

// =============================================================================
// ASYNC CHANNEL TESTS
// =============================================================================

void test_async_send_receive(void) {
    channel_config_t config = {
        .type = CHAN_TYPE_ASYNC,
        .mode = CHAN_MODE_NONBLOCKING,
        .buffer_size = 4096,
        .message_size = sizeof(test_message_t),
        .serializer = SERIAL_CAPNP_LITE
    };
    
    exo_cap_t owner_cap = create_test_capability(4, 0xFFFF);
    unified_channel_t* chan = channel_create("async_test", &config, owner_cap);
    TEST_ASSERT(chan != NULL, "Async test channel creation");
    
    // Test sending
    test_message_t sent_msg = create_test_message(42);
    int send_result = channel_send(chan, &sent_msg, sizeof(sent_msg), chan->send_cap);
    TEST_ASSERT(send_result == 0, "Async channel send");
    TEST_ASSERT(!channel_is_empty(chan), "Channel not empty after send");
    TEST_ASSERT(channel_pending_count(chan) == 1, "One pending message");
    
    // Test receiving
    test_message_t recv_msg = {0};
    size_t recv_size = sizeof(recv_msg);
    int recv_result = channel_receive(chan, &recv_msg, &recv_size, chan->recv_cap);
    TEST_ASSERT(recv_result == 0, "Async channel receive");
    TEST_ASSERT(validate_test_message(&recv_msg, &sent_msg), "Message content correct");
    TEST_ASSERT(channel_is_empty(chan), "Channel empty after receive");
    TEST_ASSERT(channel_pending_count(chan) == 0, "Zero pending messages");
    
    channel_destroy(chan);
}

void test_async_multiple_messages(void) {
    channel_config_t config = {
        .type = CHAN_TYPE_ASYNC,
        .mode = CHAN_MODE_NONBLOCKING,
        .buffer_size = 4096,
        .message_size = sizeof(test_message_t),
        .serializer = SERIAL_RAW
    };
    
    exo_cap_t owner_cap = create_test_capability(5, 0xFFFF);
    unified_channel_t* chan = channel_create("multi_async", &config, owner_cap);
    
    const int num_messages = 5;
    test_message_t sent_msgs[num_messages];
    
    // Send multiple messages
    for (int i = 0; i < num_messages; i++) {
        sent_msgs[i] = create_test_message(100 + i);
        int result = channel_send(chan, &sent_msgs[i], sizeof(sent_msgs[i]), chan->send_cap);
        TEST_ASSERT(result == 0, "Multiple send success");
    }
    
    TEST_ASSERT(channel_pending_count(chan) == num_messages, "Correct pending count");
    
    // Receive multiple messages
    for (int i = 0; i < num_messages; i++) {
        test_message_t recv_msg = {0};
        size_t recv_size = sizeof(recv_msg);
        int result = channel_receive(chan, &recv_msg, &recv_size, chan->recv_cap);
        TEST_ASSERT(result == 0, "Multiple receive success");
        TEST_ASSERT(validate_test_message(&recv_msg, &sent_msgs[i]), "Message order preserved");
    }
    
    TEST_ASSERT(channel_is_empty(chan), "Channel empty after all receives");
    
    channel_destroy(chan);
}

// =============================================================================
// CAPABILITY VALIDATION TESTS
// =============================================================================

void test_capability_validation(void) {
    channel_config_t config = {
        .type = CHAN_TYPE_ASYNC,
        .mode = CHAN_MODE_NONBLOCKING,
        .buffer_size = 1024,
        .message_size = sizeof(test_message_t),
        .serializer = SERIAL_RAW
    };
    
    exo_cap_t owner_cap = create_test_capability(6, 0xFFFF);
    unified_channel_t* chan = channel_create("cap_test", &config, owner_cap);
    
    test_message_t msg = create_test_message(123);
    
    // Test valid capabilities
    int send_result = channel_send(chan, &msg, sizeof(msg), chan->send_cap);
    TEST_ASSERT(send_result == 0, "Valid send capability");
    
    size_t recv_size = sizeof(msg);
    test_message_t recv_msg = {0};
    int recv_result = channel_receive(chan, &recv_msg, &recv_size, chan->recv_cap);
    TEST_ASSERT(recv_result == 0, "Valid receive capability");
    
    // Test invalid capabilities
    exo_cap_t invalid_cap = create_test_capability(999, 0x0000);
    
    int invalid_send = channel_send(chan, &msg, sizeof(msg), invalid_cap);
    TEST_ASSERT(invalid_send == -1, "Invalid send capability rejected");
    
    int invalid_recv = channel_receive(chan, &recv_msg, &recv_size, invalid_cap);
    TEST_ASSERT(invalid_recv == -1, "Invalid receive capability rejected");
    
    // Check error statistics
    unified_channel_t stats;
    channel_get_stats(chan, &stats);
    TEST_ASSERT(stats.errors.cap_errors >= 2, "Capability errors recorded");
    
    channel_destroy(chan);
}

// =============================================================================
// TYPED CHANNEL TESTS
// =============================================================================

void test_typed_channels(void) {
    channel_config_t config = {
        .type = CHAN_TYPE_ASYNC,
        .mode = CHAN_MODE_NONBLOCKING,
        .buffer_size = 2048,
        .serializer = SERIAL_CAPNP_LITE
    };
    
    exo_cap_t owner_cap = create_test_capability(7, 0xFFFF);
    
    // Test different typed channels
    test_channel_t* test_chan = test_channel_create("typed_test", &config, owner_cap);
    position_channel_t* pos_chan = position_channel_create("typed_pos", &config, owner_cap);
    control_channel_t* ctrl_chan = control_channel_create("typed_ctrl", &config, owner_cap);
    
    TEST_ASSERT(test_chan != NULL, "Test typed channel creation");
    TEST_ASSERT(pos_chan != NULL, "Position typed channel creation");
    TEST_ASSERT(ctrl_chan != NULL, "Control typed channel creation");
    
    // Test typed operations
    test_message_t test_msg = create_test_message(456);
    int test_send = test_channel_send(test_chan, &test_msg, test_chan->chan->send_cap);
    TEST_ASSERT(test_send == 0, "Typed test send");
    
    test_message_t test_recv = {0};
    int test_recv_result = test_channel_receive(test_chan, &test_recv, test_chan->chan->recv_cap);
    TEST_ASSERT(test_recv_result == 0, "Typed test receive");
    TEST_ASSERT(validate_test_message(&test_recv, &test_msg), "Typed message content");
    
    position_message_t pos_msg = {.x = 100, .y = 200, .z = 300, .velocity = 15.5f, .active = true};
    int pos_send = position_channel_send(pos_chan, &pos_msg, pos_chan->chan->send_cap);
    TEST_ASSERT(pos_send == 0, "Typed position send");
    
    position_message_t pos_recv = {0};
    int pos_recv_result = position_channel_receive(pos_chan, &pos_recv, pos_chan->chan->recv_cap);
    TEST_ASSERT(pos_recv_result == 0, "Typed position receive");
    TEST_ASSERT(pos_recv.x == 100 && pos_recv.y == 200 && pos_recv.z == 300, "Position data correct");
    TEST_ASSERT(pos_recv.velocity == 15.5f && pos_recv.active == true, "Position metadata correct");
    
    test_channel_destroy(test_chan);
    position_channel_destroy(pos_chan);
    control_channel_destroy(ctrl_chan);
}

// =============================================================================
// NON-BLOCKING OPERATIONS TESTS
// =============================================================================

void test_nonblocking_operations(void) {
    channel_config_t config = {
        .type = CHAN_TYPE_ASYNC,
        .mode = CHAN_MODE_BLOCKING, // Start in blocking mode
        .buffer_size = sizeof(test_message_t) * 2, // Space for 2 messages
        .message_size = sizeof(test_message_t),
        .serializer = SERIAL_RAW
    };
    
    exo_cap_t owner_cap = create_test_capability(8, 0xFFFF);
    unified_channel_t* chan = channel_create("nonblock_test", &config, owner_cap);
    
    test_message_t msg1 = create_test_message(111);
    test_message_t msg2 = create_test_message(222);
    test_message_t msg3 = create_test_message(333);
    
    // Fill the buffer
    int send1 = channel_try_send(chan, &msg1, sizeof(msg1), chan->send_cap);
    int send2 = channel_try_send(chan, &msg2, sizeof(msg2), chan->send_cap);
    TEST_ASSERT(send1 == 0, "Try send 1 success");
    TEST_ASSERT(send2 == 0, "Try send 2 success");
    
    // This should fail (buffer full)
    int send3 = channel_try_send(chan, &msg3, sizeof(msg3), chan->send_cap);
    TEST_ASSERT(send3 == -2, "Try send 3 would block");
    
    // Try receive should succeed
    test_message_t recv_msg = {0};
    size_t recv_size = sizeof(recv_msg);
    int recv1 = channel_try_receive(chan, &recv_msg, &recv_size, chan->recv_cap);
    TEST_ASSERT(recv1 == 0, "Try receive 1 success");
    TEST_ASSERT(validate_test_message(&recv_msg, &msg1), "Try receive 1 content");
    
    // Now we can send the third message
    int send3_retry = channel_try_send(chan, &msg3, sizeof(msg3), chan->send_cap);
    TEST_ASSERT(send3_retry == 0, "Try send 3 retry success");
    
    channel_destroy(chan);
}

// =============================================================================
// CHANNEL REGISTRY TESTS
// =============================================================================

void test_channel_registry(void) {
    channel_config_t config = {
        .type = CHAN_TYPE_SYNC,
        .message_size = sizeof(test_message_t),
        .serializer = SERIAL_RAW
    };
    
    exo_cap_t owner_cap = create_test_capability(9, 0xFFFF);
    
    // Create several channels
    unified_channel_t* chan1 = channel_create("registry_1", &config, owner_cap);
    unified_channel_t* chan2 = channel_create("registry_2", &config, owner_cap);
    unified_channel_t* chan3 = channel_create("registry_3", &config, owner_cap);
    
    // Test finding by name
    unified_channel_t* found1 = channel_find("registry_1");
    unified_channel_t* found2 = channel_find("registry_2");
    unified_channel_t* not_found = channel_find("nonexistent");
    
    TEST_ASSERT(found1 == chan1, "Find channel by name 1");
    TEST_ASSERT(found2 == chan2, "Find channel by name 2");
    TEST_ASSERT(not_found == NULL, "Nonexistent channel not found");
    
    // Test finding by ID
    unified_channel_t* found_by_id = channel_find_by_id(chan3->id);
    TEST_ASSERT(found_by_id == chan3, "Find channel by ID");
    
    // Test channel count
    size_t count = channel_count();
    TEST_ASSERT(count >= 3, "Channel count correct");
    
    // Test channel listing
    unified_channel_t* list[10];
    size_t listed = channel_list(list, 10);
    TEST_ASSERT(listed >= 3, "Channel list count");
    
    bool found_chan1 = false, found_chan2 = false, found_chan3 = false;
    for (size_t i = 0; i < listed; i++) {
        if (list[i] == chan1) found_chan1 = true;
        if (list[i] == chan2) found_chan2 = true;
        if (list[i] == chan3) found_chan3 = true;
    }
    TEST_ASSERT(found_chan1 && found_chan2 && found_chan3, "All channels in list");
    
    channel_destroy(chan1);
    channel_destroy(chan2);
    channel_destroy(chan3);
}

// =============================================================================
// PERFORMANCE TESTS
// =============================================================================

void test_performance_monitoring(void) {
    channel_config_t config = {
        .type = CHAN_TYPE_ASYNC,
        .mode = CHAN_MODE_NONBLOCKING,
        .buffer_size = 4096,
        .message_size = sizeof(test_message_t),
        .serializer = SERIAL_CAPNP_LITE
    };
    
    exo_cap_t owner_cap = create_test_capability(10, 0xFFFF);
    unified_channel_t* chan = channel_create("perf_test", &config, owner_cap);
    
    // Reset stats
    channel_reset_stats(chan);
    
    // Send and receive several messages
    const int num_ops = 100;
    for (int i = 0; i < num_ops; i++) {
        test_message_t msg = create_test_message(i);
        channel_send(chan, &msg, sizeof(msg), chan->send_cap);
        
        test_message_t recv_msg = {0};
        size_t recv_size = sizeof(recv_msg);
        channel_receive(chan, &recv_msg, &recv_size, chan->recv_cap);
    }
    
    // Check statistics
    unified_channel_t stats;
    channel_get_stats(chan, &stats);
    
    TEST_ASSERT(stats.stats.messages_sent == num_ops, "Send count tracked");
    TEST_ASSERT(stats.stats.messages_received == num_ops, "Receive count tracked");
    TEST_ASSERT(stats.stats.bytes_sent > 0, "Bytes sent tracked");
    TEST_ASSERT(stats.stats.bytes_received > 0, "Bytes received tracked");
    TEST_ASSERT(stats.stats.serialization_ns > 0, "Serialization time tracked");
    
    printf("Performance stats:\n");
    printf("  Messages: %lu sent, %lu received\n", 
           stats.stats.messages_sent, stats.stats.messages_received);
    printf("  Bytes: %lu sent, %lu received\n",
           stats.stats.bytes_sent, stats.stats.bytes_received);
    printf("  Avg serialization time: %lu ns\n", 
           stats.stats.serialization_ns / (num_ops * 2));
    
    channel_destroy(chan);
}

// =============================================================================
// SERIALIZATION TESTS
// =============================================================================

void test_serialization_layers(void) {
    // Test each serialization layer
    test_message_t original = create_test_message(999);
    uint8_t buffer[1024];
    test_message_t decoded = {0};
    
    // Test raw serializer
    size_t raw_encoded = raw_serializer.encode(&original, sizeof(original), buffer, sizeof(buffer));
    TEST_ASSERT(raw_encoded == sizeof(original), "Raw serialization size");
    
    size_t raw_decoded = raw_serializer.decode(buffer, raw_encoded, &decoded, sizeof(decoded));
    TEST_ASSERT(raw_decoded == sizeof(original), "Raw deserialization size");
    TEST_ASSERT(validate_test_message(&decoded, &original), "Raw serialization content");
    
    // Test Cap'n Proto Lite serializer
    memset(buffer, 0, sizeof(buffer));
    memset(&decoded, 0, sizeof(decoded));
    
    size_t lite_encoded = capnp_lite_serializer.encode(&original, sizeof(original), buffer, sizeof(buffer));
    TEST_ASSERT(lite_encoded > sizeof(original), "Lite serialization has overhead");
    TEST_ASSERT(capnp_lite_serializer.validate(buffer, lite_encoded), "Lite serialization validates");
    
    size_t lite_decoded = capnp_lite_serializer.decode(buffer, lite_encoded, &decoded, sizeof(decoded));
    TEST_ASSERT(lite_decoded == sizeof(original), "Lite deserialization size");
    TEST_ASSERT(validate_test_message(&decoded, &original), "Lite serialization content");
    
    // Test Cap'n Proto Full serializer
    memset(buffer, 0, sizeof(buffer));
    memset(&decoded, 0, sizeof(decoded));
    
    size_t full_encoded = capnp_full_serializer.encode(&original, sizeof(original), buffer, sizeof(buffer));
    TEST_ASSERT(full_encoded > 0, "Full serialization succeeds");
    TEST_ASSERT(capnp_full_serializer.validate(buffer, full_encoded), "Full serialization validates");
    
    size_t full_decoded = capnp_full_serializer.decode(buffer, full_encoded, &decoded, sizeof(decoded));
    TEST_ASSERT(full_decoded > 0, "Full deserialization succeeds");
}

// =============================================================================
// ERROR HANDLING TESTS
// =============================================================================

void test_error_conditions(void) {
    channel_config_t config = {
        .type = CHAN_TYPE_ASYNC,
        .mode = CHAN_MODE_NONBLOCKING,
        .buffer_size = 1024,
        .message_size = sizeof(test_message_t),
        .serializer = SERIAL_CAPNP_LITE
    };
    
    exo_cap_t owner_cap = create_test_capability(11, 0xFFFF);
    unified_channel_t* chan = channel_create("error_test", &config, owner_cap);
    
    test_message_t msg = create_test_message(777);
    
    // Test NULL parameter errors
    int null_send = channel_send(NULL, &msg, sizeof(msg), chan->send_cap);
    TEST_ASSERT(null_send == -1, "NULL channel send fails");
    
    int null_msg_send = channel_send(chan, NULL, sizeof(msg), chan->send_cap);
    TEST_ASSERT(null_msg_send == -1, "NULL message send fails");
    
    size_t recv_size = sizeof(msg);
    int null_recv = channel_receive(chan, NULL, &recv_size, chan->recv_cap);
    TEST_ASSERT(null_recv == -1, "NULL receive buffer fails");
    
    // Test oversized message
    char big_buffer[4096];
    int oversized_send = channel_send(chan, big_buffer, sizeof(big_buffer), chan->send_cap);
    TEST_ASSERT(oversized_send == -1, "Oversized message rejected");
    
    // Test receive from empty channel (non-blocking)
    test_message_t recv_msg = {0};
    recv_size = sizeof(recv_msg);
    int empty_recv = channel_try_receive(chan, &recv_msg, &recv_size, chan->recv_cap);
    TEST_ASSERT(empty_recv == -2, "Empty channel receive would block");
    
    channel_destroy(chan);
}

// =============================================================================
// STRESS TESTS
// =============================================================================

void test_stress_async_channel(void) {
    printf("Running stress test (this may take a moment)...\n");
    
    channel_config_t config = {
        .type = CHAN_TYPE_ASYNC,
        .mode = CHAN_MODE_NONBLOCKING,
        .buffer_size = 16384, // Large buffer
        .message_size = sizeof(test_message_t),
        .serializer = SERIAL_RAW // Fastest for stress test
    };
    
    exo_cap_t owner_cap = create_test_capability(12, 0xFFFF);
    unified_channel_t* chan = channel_create("stress_test", &config, owner_cap);
    
    const int stress_messages = 1000;
    int send_success = 0;
    int recv_success = 0;
    
    // Stress test: rapid send/receive
    clock_t start = clock();
    
    for (int i = 0; i < stress_messages; i++) {
        test_message_t msg = create_test_message(i);
        if (channel_try_send(chan, &msg, sizeof(msg), chan->send_cap) == 0) {
            send_success++;
        }
        
        test_message_t recv_msg = {0};
        size_t recv_size = sizeof(recv_msg);
        if (channel_try_receive(chan, &recv_msg, &recv_size, chan->recv_cap) == 0) {
            recv_success++;
        }
    }
    
    // Drain remaining messages
    while (!channel_is_empty(chan)) {
        test_message_t recv_msg = {0};
        size_t recv_size = sizeof(recv_msg);
        if (channel_try_receive(chan, &recv_msg, &recv_size, chan->recv_cap) == 0) {
            recv_success++;
        }
    }
    
    clock_t end = clock();
    double elapsed = ((double)(end - start)) / CLOCKS_PER_SEC;
    
    TEST_ASSERT(send_success > 0, "Stress test sent messages");
    TEST_ASSERT(recv_success > 0, "Stress test received messages");
    TEST_ASSERT(channel_is_empty(chan), "Channel empty after stress test");
    
    printf("Stress test completed in %.3f seconds\n", elapsed);
    printf("  Sent: %d messages\n", send_success);
    printf("  Received: %d messages\n", recv_success);
    
    // Check for memory leaks by getting stats
    unified_channel_t stats;
    channel_get_stats(chan, &stats);
    printf("  Errors: %lu send, %lu recv, %lu serial, %lu cap\n",
           stats.errors.send_errors, stats.errors.recv_errors,
           stats.errors.serial_errors, stats.errors.cap_errors);
    
    channel_destroy(chan);
}

// =============================================================================
// MAIN TEST RUNNER
// =============================================================================

int main(int argc, char* argv[]) {
    printf("FeuerBird Unified Channel System Test Suite\n");
    printf("===========================================\n");
    
    // Initialize the channel system
    init_channel_system();
    
    // Run all tests
    RUN_TEST(test_channel_creation_destruction);
    RUN_TEST(test_async_channel_creation);
    RUN_TEST(test_serializer_selection);
    RUN_TEST(test_async_send_receive);
    RUN_TEST(test_async_multiple_messages);
    RUN_TEST(test_capability_validation);
    RUN_TEST(test_typed_channels);
    RUN_TEST(test_nonblocking_operations);
    RUN_TEST(test_channel_registry);
    RUN_TEST(test_performance_monitoring);
    RUN_TEST(test_serialization_layers);
    RUN_TEST(test_error_conditions);
    RUN_TEST(test_stress_async_channel);
    
    // Print summary
    printf("\n=== Test Summary ===\n");
    printf("Passed:  %d\n", tests_passed);
    printf("Failed:  %d\n", tests_failed);
    printf("Skipped: %d\n", tests_skipped);
    printf("Total:   %d\n", tests_passed + tests_failed + tests_skipped);
    
    if (tests_failed == 0) {
        printf("\n🎉 All tests passed! The unified channel system is working correctly.\n");
    } else {
        printf("\n❌ Some tests failed. Please review the implementation.\n");
    }
    
    // Cleanup
    shutdown_channel_system();
    
    return tests_failed == 0 ? 0 : 1;
}