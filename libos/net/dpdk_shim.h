#pragma once

int libos_dpdk_init(int argc, char **argv);
int libos_dpdk_tx(void *buf, int len);
int libos_dpdk_rx(void *buf, int len);
