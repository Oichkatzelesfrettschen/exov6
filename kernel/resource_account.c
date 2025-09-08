/**
 * @file resource_account.c
 * @brief Superforce-based resource accounting for exokernel
 * Uses Pais Superforce theory (c^4/G) for energy quantum accounting
 */

#include "defs.h"
#include "cap.h"
#include "exo.h"
#include <stdint.h>

/* Exokernel resource account structure */
typedef struct exo_account {
    uint64_t energy_used;     /* Energy consumed in Planck units */
    uint64_t fuel_consumed;   /* Fuel consumed for lambda execution */
    uint32_t capability_count; /* Number of active capabilities */
} exo_account_t;

/**
 * Initialize exokernel account with Superforce energy allocation
 * SF ~ c^4/G ~ 10^44 N provides the fundamental energy gradient
 */
void exo_account_init(exo_account_t *a) {
    if (a) {
        a->energy_used = 0;
        a->fuel_consumed = 0;
        a->capability_count = 0;
    }
}

/**
 * Charge account with Superforce energy units
 * Each unit represents one Planck energy quantum
 */
void exo_account_charge(exo_account_t *a, uint64_t energy_quanta) {
    if (a) {
        a->energy_used += energy_quanta;
    }
}

/**
 * Account for lambda execution fuel consumption
 * Links to our Pi-calculus lambda capability system
 */
void exo_account_fuel(exo_account_t *a, uint32_t fuel_amount) {
    if (a) {
        a->fuel_consumed += fuel_amount;
    }
}

uint64_t mk_account_usage(const exo_account_t *a) {
    return a ? a->energy_used : 0;
}
