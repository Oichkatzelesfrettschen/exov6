#pragma once

#include <stdatomic.h>
#include <stdint.h>
#include <stdbool.h>
#include "ultimate_lock_synthesis.h"

/**
 * @file genetic_lock_evolution.h
 * @brief Genetic Algorithm Evolution Engine for Lock Synchronization Primitives
 * 
 * This module implements a revolutionary genetic algorithm system that automatically
 * evolves and optimizes lock algorithms in real-time based on workload patterns,
 * performance metrics, and environmental pressures. Lock behaviors are encoded as
 * genetic chromosomes that undergo natural selection, mutation, and crossover to
 * produce superior synchronization primitives.
 */

// Genetic Algorithm Configuration
#define LOCK_GENE_POOL_SIZE        256     // Population size
#define LOCK_CHROMOSOME_LENGTH     64      // Genes per algorithm
#define LOCK_MUTATION_RATE         0.05f   // 5% mutation probability
#define LOCK_CROSSOVER_RATE        0.7f    // 70% crossover probability
#define LOCK_ELITE_PRESERVATION    0.1f    // Preserve top 10%
#define LOCK_GENERATION_CYCLES     1000    // Breeding cycles before reset
#define LOCK_FITNESS_HISTORY       128     // Performance samples per algorithm

// Gene Types and Ranges
#define GENE_TYPE_BACKOFF          0x01    // Backoff strategy genes
#define GENE_TYPE_FAIRNESS         0x02    // Fairness algorithm genes
#define GENE_TYPE_CONTENTION       0x03    // Contention handling genes
#define GENE_TYPE_TIMING           0x04    // Timing parameter genes
#define GENE_TYPE_MEMORY_ORDER     0x05    // Memory ordering genes
#define GENE_TYPE_ADAPTIVE         0x06    // Adaptive behavior genes

/**
 * @brief Single gene representing a lock algorithm parameter
 */
typedef struct lock_gene {
    uint8_t type;          // Gene type (GENE_TYPE_*)
    uint8_t allele;        // Gene value (0-255)
    uint8_t dominance;     // Expression strength (0-255)
    uint8_t stability;     // Mutation resistance (0-255)
} lock_gene_t;

/**
 * @brief Chromosome representing a complete lock algorithm
 */
typedef struct lock_chromosome {
    _Alignas(64)
    
    // Genetic sequence
    lock_gene_t genes[LOCK_CHROMOSOME_LENGTH];
    
    // Identity and lineage
    uint64_t organism_id;
    uint64_t generation;
    uint64_t parent_a_id;
    uint64_t parent_b_id;
    
    // Fitness metrics
    struct {
        float current_fitness;      // Current performance score
        float average_fitness;      // Historical average
        float peak_fitness;         // Best ever achieved
        float fitness_variance;     // Stability measure
        uint32_t evaluation_count;  // Number of fitness tests
        uint64_t total_runtime_ns;  // Total execution time
    } fitness;
    
    // Performance characteristics (phenotype)
    struct {
        uint32_t avg_acquisition_cycles;   // Average lock acquisition time
        uint32_t max_acquisition_cycles;   // Worst-case acquisition time
        float contention_efficiency;       // Performance under contention
        float fairness_coefficient;        // FIFO fairness measure
        float cache_efficiency;            // Cache line bounce reduction
        float numa_locality;               // NUMA node affinity
        uint32_t false_sharing_penalty;    // False sharing cost
    } phenotype;
    
    // Environmental adaptation
    struct {
        uint32_t preferred_workloads;      // Bitmask of optimal workload types
        uint32_t cpu_affinity;             // Preferred CPU architectures
        float temperature_tolerance;       // Thermal throttling resistance
        float power_efficiency;            // Energy consumption per operation
    } environment;
    
    // Evolutionary metadata
    atomic_uint32_t reference_count;      // Usage reference counter
    atomic_uint64_t last_used_time;       // Last deployment timestamp
    atomic_uint32_t deployment_count;     // Number of times deployed
    
} lock_chromosome_t;

/**
 * @brief Gene pool population management
 */
typedef struct genetic_population {
    _Alignas(128)
    
    // Current population
    lock_chromosome_t organisms[LOCK_GENE_POOL_SIZE];
    atomic_uint32_t population_size;
    
    // Elite preservation (hall of fame)
    lock_chromosome_t elite[LOCK_GENE_POOL_SIZE / 10];
    atomic_uint32_t elite_count;
    
    // Generation tracking
    atomic_uint64_t current_generation;
    atomic_uint64_t total_evaluations;
    atomic_uint64_t successful_mutations;
    atomic_uint64_t successful_crossovers;
    
    // Population diversity metrics
    struct {
        float genetic_diversity;         // Shannon entropy of gene distribution
        float phenotypic_diversity;      // Behavioral variation measure
        float fitness_spread;            // Range of fitness values
        uint32_t species_count;          // Number of distinct species
    } diversity;
    
    // Environmental pressures
    struct {
        float selection_pressure;        // How aggressively to select
        float mutation_pressure;         // Environmental mutation rate
        float convergence_pressure;      // Pressure to converge/diversify
        uint32_t current_workload_type;  // Active workload pattern
    } environment;
    
} genetic_population_t;

/**
 * @brief Fitness evaluation context
 */
typedef struct fitness_evaluator {
    // Workload simulation parameters
    struct {
        uint32_t thread_count;           // Number of competing threads
        uint32_t critical_section_ns;    // Average critical section duration
        float contention_probability;    // Likelihood of contention
        uint32_t numa_nodes;             // Number of NUMA nodes
        uint32_t cache_line_size;        // CPU cache line size
    } workload;
    
    // Performance measurement infrastructure
    struct {
        uint64_t start_time;             // Evaluation start timestamp
        uint64_t end_time;               // Evaluation end timestamp
        uint32_t sample_count;           // Number of measurements
        float measurements[LOCK_FITNESS_HISTORY]; // Raw performance data
    } measurement;
    
    // Fitness calculation weights
    struct {
        float throughput_weight;         // Emphasize raw speed
        float fairness_weight;           // Emphasize fairness
        float latency_weight;            // Emphasize low latency
        float scalability_weight;        // Emphasize scaling behavior
        float power_weight;              // Emphasize energy efficiency
    } weights;
    
} fitness_evaluator_t;

/**
 * @brief Evolutionary engine state
 */
typedef struct genetic_evolution_engine {
    _Alignas(256)
    
    // Core genetic components
    genetic_population_t population;
    fitness_evaluator_t evaluator;
    
    // Evolution control
    atomic_uint32_t evolution_enabled;
    atomic_uint32_t breeding_in_progress;
    atomic_uint64_t last_evolution_time;
    
    // Algorithm deployment
    struct {
        lock_chromosome_t *active_algorithms[META_LOCK_TYPE_MAX];
        atomic_uint32_t deployment_generation[META_LOCK_TYPE_MAX];
        uint64_t last_deployment_time[META_LOCK_TYPE_MAX];
    } deployment;
    
    // Performance monitoring
    struct {
        atomic_uint64_t total_evolutions;
        atomic_uint64_t successful_deployments;
        atomic_uint64_t algorithm_improvements;
        float average_fitness_gain;
        uint64_t best_fitness_ever;
    } statistics;
    
    // Real-time adaptation
    struct {
        uint32_t current_workload_signature; // Hash of current workload
        float adaptation_rate;                // Speed of environmental response
        uint32_t stability_threshold;        // Minimum generations before change
        float novelty_bonus;                  // Reward for innovative solutions
    } adaptation;
    
} genetic_evolution_engine_t;

// API Functions

/**
 * @brief Initialize genetic evolution engine
 * @param engine Pointer to evolution engine
 * @return 0 on success, negative errno on failure
 */
int genetic_evolution_init(genetic_evolution_engine_t *engine);

/**
 * @brief Create initial random population
 * @param population Pointer to population structure
 * @param seed Random seed for reproducibility
 * @return 0 on success, negative errno on failure
 */
int genetic_population_initialize(genetic_population_t *population, uint64_t seed);

/**
 * @brief Evaluate fitness of a lock chromosome
 * @param chromosome Lock algorithm to evaluate
 * @param evaluator Fitness evaluation context
 * @param workload_type Type of workload to test against
 * @return Fitness score (0.0-1.0), negative errno on error
 */
float genetic_evaluate_fitness(lock_chromosome_t *chromosome,
                              fitness_evaluator_t *evaluator,
                              uint32_t workload_type);

/**
 * @brief Perform genetic crossover between two parent chromosomes
 * @param parent_a First parent chromosome
 * @param parent_b Second parent chromosome
 * @param offspring Output chromosome (child)
 * @return 0 on success, negative errno on failure
 */
int genetic_crossover(const lock_chromosome_t *parent_a,
                     const lock_chromosome_t *parent_b,
                     lock_chromosome_t *offspring);

/**
 * @brief Apply random mutations to a chromosome
 * @param chromosome Chromosome to mutate
 * @param mutation_rate Probability of mutation per gene (0.0-1.0)
 * @return Number of mutations applied
 */
int genetic_mutate(lock_chromosome_t *chromosome, float mutation_rate);

/**
 * @brief Select parents for breeding using fitness-proportionate selection
 * @param population Current population
 * @param parent_a Output first parent
 * @param parent_b Output second parent
 * @return 0 on success, negative errno on failure
 */
int genetic_select_parents(genetic_population_t *population,
                          lock_chromosome_t **parent_a,
                          lock_chromosome_t **parent_b);

/**
 * @brief Execute one generation of evolution
 * @param engine Evolution engine
 * @return 0 on success, negative errno on failure
 */
int genetic_evolve_generation(genetic_evolution_engine_t *engine);

/**
 * @brief Deploy evolved algorithm to ultimate lock framework
 * @param engine Evolution engine
 * @param lock_type Target lock type to replace
 * @param chromosome Evolved algorithm to deploy
 * @return 0 on success, negative errno on failure
 */
int genetic_deploy_algorithm(genetic_evolution_engine_t *engine,
                            meta_lock_type_t lock_type,
                            lock_chromosome_t *chromosome);

// Chromosome Manipulation

/**
 * @brief Encode lock behavior parameters into genetic representation
 * @param behavior Lock behavior specification
 * @param chromosome Output chromosome
 * @return 0 on success, negative errno on failure
 */
int genetic_encode_behavior(const void *behavior, lock_chromosome_t *chromosome);

/**
 * @brief Decode genetic representation into executable lock behavior
 * @param chromosome Input chromosome
 * @param behavior Output behavior specification
 * @return 0 on success, negative errno on failure
 */
int genetic_decode_behavior(const lock_chromosome_t *chromosome, void *behavior);

/**
 * @brief Calculate genetic distance between two chromosomes
 * @param chromosome_a First chromosome
 * @param chromosome_b Second chromosome
 * @return Genetic distance (0.0-1.0), negative errno on error
 */
float genetic_calculate_distance(const lock_chromosome_t *chromosome_a,
                                const lock_chromosome_t *chromosome_b);

// Population Management

/**
 * @brief Add new organism to population
 * @param population Target population
 * @param chromosome New organism to add
 * @return 0 on success, negative errno on failure
 */
int genetic_population_add(genetic_population_t *population,
                          const lock_chromosome_t *chromosome);

/**
 * @brief Remove least fit organisms from population
 * @param population Target population
 * @param removal_count Number of organisms to remove
 * @return Number actually removed
 */
int genetic_population_cull(genetic_population_t *population, uint32_t removal_count);

/**
 * @brief Preserve elite organisms across generations
 * @param population Target population
 * @return 0 on success, negative errno on failure
 */
int genetic_preserve_elite(genetic_population_t *population);

/**
 * @brief Calculate population diversity metrics
 * @param population Target population
 * @return 0 on success, negative errno on failure
 */
int genetic_calculate_diversity(genetic_population_t *population);

// Advanced Evolution Features

/**
 * @brief Implement island model with migration between subpopulations
 * @param populations Array of island populations
 * @param island_count Number of islands
 * @param migration_rate Rate of inter-island migration
 * @return 0 on success, negative errno on failure
 */
int genetic_island_migration(genetic_population_t *populations,
                             uint32_t island_count,
                             float migration_rate);

/**
 * @brief Apply speciation to maintain genetic diversity
 * @param population Target population
 * @param compatibility_threshold Species compatibility threshold
 * @return Number of species formed
 */
int genetic_speciation(genetic_population_t *population,
                      float compatibility_threshold);

/**
 * @brief Implement adaptive mutation rates based on population convergence
 * @param population Target population
 * @return New mutation rate
 */
float genetic_adaptive_mutation_rate(genetic_population_t *population);

/**
 * @brief Co-evolution between competing lock algorithms
 * @param population_a First competing population
 * @param population_b Second competing population
 * @return 0 on success, negative errno on failure
 */
int genetic_coevolution(genetic_population_t *population_a,
                       genetic_population_t *population_b);

// Real-Time Integration

/**
 * @brief Monitor system performance and trigger evolution
 * @param engine Evolution engine
 * @param performance_threshold Minimum performance threshold
 * @return 0 if evolution triggered, positive if not needed, negative errno on error
 */
int genetic_adaptive_evolution(genetic_evolution_engine_t *engine,
                              float performance_threshold);

/**
 * @brief Hot-swap lock algorithms without disrupting running system
 * @param old_algorithm Algorithm to replace
 * @param new_algorithm Evolved replacement algorithm
 * @return 0 on success, negative errno on failure
 */
int genetic_hot_swap_algorithm(lock_chromosome_t *old_algorithm,
                              lock_chromosome_t *new_algorithm);

/**
 * @brief Rollback to previous algorithm if evolved version underperforms
 * @param engine Evolution engine
 * @param lock_type Lock type to rollback
 * @return 0 on success, negative errno on failure
 */
int genetic_rollback_algorithm(genetic_evolution_engine_t *engine,
                              meta_lock_type_t lock_type);

// Statistics and Analysis

/**
 * @brief Get comprehensive evolution statistics
 * @param engine Evolution engine
 * @param stats Output statistics structure
 * @return 0 on success, negative errno on failure
 */
int genetic_get_evolution_stats(const genetic_evolution_engine_t *engine,
                               struct genetic_evolution_stats *stats);

/**
 * @brief Export population genealogy for analysis
 * @param population Target population
 * @param genealogy Output genealogy tree
 * @return 0 on success, negative errno on failure
 */
int genetic_export_genealogy(const genetic_population_t *population,
                            struct genetic_genealogy *genealogy);

/**
 * @brief Visualize genetic diversity and fitness landscape
 * @param population Target population
 * @param visualization Output visualization data
 * @return 0 on success, negative errno on failure
 */
int genetic_visualize_population(const genetic_population_t *population,
                                struct genetic_visualization *visualization);

// Configuration and Tuning

/**
 * @brief Configure evolutionary parameters
 * @param engine Evolution engine
 * @param config Configuration parameters
 * @return 0 on success, negative errno on failure
 */
int genetic_configure_evolution(genetic_evolution_engine_t *engine,
                               const struct genetic_config *config);

/**
 * @brief Set fitness evaluation weights for different objectives
 * @param evaluator Fitness evaluator
 * @param weights Objective weights structure
 * @return 0 on success, negative errno on failure
 */
int genetic_set_fitness_weights(fitness_evaluator_t *evaluator,
                               const struct fitness_weights *weights);

/**
 * @brief Enable/disable specific evolutionary mechanisms
 * @param engine Evolution engine
 * @param mechanisms Bitmask of mechanisms to enable/disable
 * @return 0 on success, negative errno on failure
 */
int genetic_configure_mechanisms(genetic_evolution_engine_t *engine,
                                uint64_t mechanisms);

// Genetic Lock Execution Functions

/**
 * @brief Execute genetically evolved lock acquisition
 * @param chromosome Evolved algorithm chromosome
 * @param lock Target ultimate lock
 * @param timeout_ns Maximum wait time in nanoseconds
 * @return 0 on success, negative errno on failure
 */
int genetic_execute_evolved_acquire(struct lock_chromosome *chromosome,
                                   struct ultimate_lock *lock,
                                   uint64_t timeout_ns);

/**
 * @brief Execute genetically evolved lock release
 * @param chromosome Evolved algorithm chromosome
 * @param lock Target ultimate lock
 * @return 0 on success, negative errno on failure
 */
int genetic_execute_evolved_release(struct lock_chromosome *chromosome,
                                   struct ultimate_lock *lock);

/**
 * @brief Initialize genetic evolution subsystem
 */
void genetic_evolution_subsystem_init(void);

// Mechanism flags for genetic_configure_mechanisms
#define GENETIC_MECHANISM_CROSSOVER         (1ULL << 0)
#define GENETIC_MECHANISM_MUTATION          (1ULL << 1)
#define GENETIC_MECHANISM_ELITE_PRESERVE    (1ULL << 2)
#define GENETIC_MECHANISM_SPECIATION        (1ULL << 3)
#define GENETIC_MECHANISM_ISLAND_MODEL      (1ULL << 4)
#define GENETIC_MECHANISM_COEVOLUTION       (1ULL << 5)
#define GENETIC_MECHANISM_ADAPTIVE_MUTATION (1ULL << 6)
#define GENETIC_MECHANISM_HOT_SWAP          (1ULL << 7)
#define GENETIC_MECHANISM_AUTO_ROLLBACK     (1ULL << 8)

// Workload types for fitness evaluation
#define WORKLOAD_TYPE_CPU_INTENSIVE         0x01
#define WORKLOAD_TYPE_IO_INTENSIVE          0x02
#define WORKLOAD_TYPE_MEMORY_INTENSIVE      0x04
#define WORKLOAD_TYPE_NETWORK_INTENSIVE     0x08
#define WORKLOAD_TYPE_LOW_CONTENTION        0x10
#define WORKLOAD_TYPE_HIGH_CONTENTION       0x20
#define WORKLOAD_TYPE_NUMA_DISTRIBUTED      0x40
#define WORKLOAD_TYPE_REAL_TIME             0x80

// Statistics structures
struct genetic_evolution_stats {
    uint64_t total_generations;
    uint64_t total_evaluations;
    uint64_t successful_mutations;
    uint64_t successful_crossovers;
    uint64_t deployments;
    uint64_t rollbacks;
    float average_fitness;
    float peak_fitness;
    float population_diversity;
    uint32_t active_species;
    uint64_t evolution_time_ms;
};

struct genetic_genealogy {
    uint64_t organism_count;
    uint64_t generation_count;
    float average_lineage_depth;
    float genetic_bottleneck_factor;
    uint64_t most_successful_lineage;
};

struct genetic_visualization {
    float fitness_landscape[256][256];
    float diversity_over_time[1000];
    uint32_t species_colors[LOCK_GENE_POOL_SIZE];
    float migration_flows[16][16];
};

struct genetic_config {
    float mutation_rate;
    float crossover_rate;
    float elite_preservation_rate;
    uint32_t population_size;
    uint32_t max_generations;
    float selection_pressure;
    float novelty_bonus;
    uint32_t stability_threshold;
};

struct fitness_weights {
    float throughput;
    float latency;
    float fairness;
    float scalability;
    float power_efficiency;
    float numa_locality;
    float cache_efficiency;
};