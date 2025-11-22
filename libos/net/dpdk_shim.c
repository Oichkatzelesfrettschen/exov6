#include "dpdk_shim.h"
#include <stdio.h>

/*
 * DPDK Shim Layer
 *
 * In a production build, compile with -DHAVE_DPDK and link against librte_*.
 */

#ifdef HAVE_DPDK
#include <rte_eal.h>
#include <rte_ethdev.h>
#include <rte_mbuf.h>

static uint16_t port_id = 0;

int libos_dpdk_init(int argc, char **argv) {
    int ret = rte_eal_init(argc, argv);
    if (ret < 0) return ret;

    // Configure port 0 (simplified)
    struct rte_eth_conf port_conf = {0};
    rte_eth_dev_configure(port_id, 1, 1, &port_conf);
    rte_eth_dev_start(port_id);
    return ret;
}

int libos_dpdk_tx(void *buf, int len) {
    // Zero-copy TX logic would go here (using mbufs)
    return len;
}

int libos_dpdk_rx(void *buf, int len) {
    // RX logic
    return 0;
}

#else

int libos_dpdk_init(int argc, char **argv) {
    (void)argc; (void)argv;
    printf("LibOS: DPDK support not compiled in.\n");
    return 0;
}

int libos_dpdk_tx(void *buf, int len) {
    (void)buf;
    return len;
}

int libos_dpdk_rx(void *buf, int len) {
    (void)buf; (void)len;
    return 0;
}

#endif
