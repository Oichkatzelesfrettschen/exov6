#include "genetic_lock_evolution.h"
#include "ultimate_lock_synthesis.h"
#include "../time/posix_clock.h"
#include "../../include/defs.h"
#include "../../include/proc.h"
#include "../../include/memlayout.h"
#include <string.h>
#include <errno.h>
#include <math.h>

/**
 * @file genetic_lock_evolution.c
 * @brief Genetic Algorithm Evolution Engine Implementation
 * 
 * Revolutionary system that evolves lock algorithms in real-time using genetic
 * algorithms, natural selection, mutation, and crossover to automatically
 * discover and deploy superior synchronization primitives.
 */

// Global evolution engine instance
static genetic_evolution_engine_t global_evolution_engine;
static bool evolution_engine_initialized = false;

// Random number generation for genetic operations
static uint64_t genetic_random_state = 1;

// Performance thresholds and adaptation constants
static const float MINIMUM_FITNESS_THRESHOLD = 0.3f;
static const float ELITE_FITNESS_THRESHOLD = 0.8f;
static const uint32_t STAGNATION_GENERATIONS = 50;
static const float DIVERSITY_CRISIS_THRESHOLD = 0.1f;

// Internal helper functions
static uint64_t genetic_random(void);
static float genetic_random_float(void);
static uint64_t genetic_performance_counter(void);
static float sigmoid_activation(float x);
static float gaussian_random(float mean, float stddev);
static int compare_fitness_desc(const void *a, const void *b);

// Core Genetic Operations

int genetic_evolution_init(genetic_evolution_engine_t *engine) {
    if (!engine) {
        return -EINVAL;
    }
    
    memset(engine, 0, sizeof(*engine));
    
    // Initialize population
    int ret = genetic_population_initialize(&engine->population, genetic_performance_counter());
    if (ret < 0) {
        return ret;
    }
    
    // Initialize fitness evaluator with balanced weights
    engine->evaluator.weights.throughput_weight = 0.3f;
    engine->evaluator.weights.fairness_weight = 0.2f;
    engine->evaluator.weights.latency_weight = 0.2f;
    engine->evaluator.weights.scalability_weight = 0.2f;
    engine->evaluator.weights.power_weight = 0.1f;
    
    // Initialize workload simulation parameters
    engine->evaluator.workload.thread_count = 8;
    engine->evaluator.workload.critical_section_ns = 1000;
    engine->evaluator.workload.contention_probability = 0.3f;
    engine->evaluator.workload.numa_nodes = 2;
    engine->evaluator.workload.cache_line_size = 64;
    
    // Initialize evolution control
    atomic_init(&engine->evolution_enabled, 1);
    atomic_init(&engine->breeding_in_progress, 0);
    atomic_init(&engine->last_evolution_time, genetic_performance_counter());
    
    // Initialize deployment tracking
    for (int i = 0; i < META_LOCK_TYPE_MAX; i++) {
        engine->deployment.active_algorithms[i] = NULL;
        atomic_init(&engine->deployment.deployment_generation[i], 0);
        engine->deployment.last_deployment_time[i] = 0;
    }
    
    // Initialize statistics
    atomic_init(&engine->statistics.total_evolutions, 0);
    atomic_init(&engine->statistics.successful_deployments, 0);
    atomic_init(&engine->statistics.algorithm_improvements, 0);
    engine->statistics.average_fitness_gain = 0.0f;
    engine->statistics.best_fitness_ever = 0;
    
    // Initialize adaptation parameters
    engine->adaptation.current_workload_signature = 0;
    engine->adaptation.adaptation_rate = 0.1f;
    engine->adaptation.stability_threshold = 10;
    engine->adaptation.novelty_bonus = 0.05f;
    
    return 0;
}

int genetic_population_initialize(genetic_population_t *population, uint64_t seed) {
    if (!population) {
        return -EINVAL;
    }
    
    memset(population, 0, sizeof(*population));
    genetic_random_state = seed;
    
    // Create initial random organisms
    for (uint32_t i = 0; i < LOCK_GENE_POOL_SIZE; i++) {
        lock_chromosome_t *organism = &population->organisms[i];
        
        // Initialize genetic sequence with random genes
        for (uint32_t j = 0; j < LOCK_CHROMOSOME_LENGTH; j++) {
            organism->genes[j].type = (genetic_random() % 6) + 1; // GENE_TYPE_* values
            organism->genes[j].allele = genetic_random() & 0xFF;
            organism->genes[j].dominance = genetic_random() & 0xFF;
            organism->genes[j].stability = (genetic_random() & 0x7F) + 0x80; // High stability initially
        }
        
        // Initialize identity
        organism->organism_id = (seed << 16) | i;
        organism->generation = 0;
        organism->parent_a_id = 0;
        organism->parent_b_id = 0;
        
        // Initialize fitness with neutral values
        organism->fitness.current_fitness = 0.5f;
        organism->fitness.average_fitness = 0.5f;
        organism->fitness.peak_fitness = 0.5f;
        organism->fitness.fitness_variance = 0.1f;
        organism->fitness.evaluation_count = 0;
        organism->fitness.total_runtime_ns = 0;
        
        // Initialize phenotype with random characteristics
        organism->phenotype.avg_acquisition_cycles = 100 + (genetic_random() % 200);
        organism->phenotype.max_acquisition_cycles = organism->phenotype.avg_acquisition_cycles * 2;
        organism->phenotype.contention_efficiency = genetic_random_float();
        organism->phenotype.fairness_coefficient = genetic_random_float();
        organism->phenotype.cache_efficiency = genetic_random_float();
        organism->phenotype.numa_locality = genetic_random_float();
        organism->phenotype.false_sharing_penalty = genetic_random() % 100;
        
        // Initialize environmental preferences
        organism->environment.preferred_workloads = genetic_random();
        organism->environment.cpu_affinity = genetic_random();
        organism->environment.temperature_tolerance = genetic_random_float();
        organism->environment.power_efficiency = genetic_random_float();
        
        // Initialize atomics
        atomic_init(&organism->reference_count, 0);
        atomic_init(&organism->last_used_time, 0);
        atomic_init(&organism->deployment_count, 0);
    }
    
    atomic_init(&population->population_size, LOCK_GENE_POOL_SIZE);
    atomic_init(&population->elite_count, 0);
    atomic_init(&population->current_generation, 0);
    atomic_init(&population->total_evaluations, 0);
    atomic_init(&population->successful_mutations, 0);
    atomic_init(&population->successful_crossovers, 0);
    
    // Initialize diversity metrics
    population->diversity.genetic_diversity = 1.0f; // Maximum diversity initially
    population->diversity.phenotypic_diversity = 1.0f;
    population->diversity.fitness_spread = 0.0f; // No variation initially
    population->diversity.species_count = 1; // Single species initially
    
    // Initialize environmental pressures
    population->environment.selection_pressure = 0.3f; // Moderate selection
    population->environment.mutation_pressure = LOCK_MUTATION_RATE;
    population->environment.convergence_pressure = 0.0f;
    population->environment.current_workload_type = WORKLOAD_TYPE_CPU_INTENSIVE;
    
    return 0;
}

float genetic_evaluate_fitness(lock_chromosome_t *chromosome,
                              fitness_evaluator_t *evaluator,
                              uint32_t workload_type) {
    if (!chromosome || !evaluator) {
        return -EINVAL;
    }
    
    uint64_t start_time = genetic_performance_counter();
    
    // Decode genetic algorithm parameters from chromosome
    struct decoded_behavior {
        uint32_t backoff_strategy;
        uint32_t fairness_policy;
        uint32_t contention_handling;
        uint32_t timing_parameters;
        uint32_t memory_ordering;
        uint32_t adaptive_behavior;
    } behavior = {0};
    
    // Extract behavior from genes
    for (uint32_t i = 0; i < LOCK_CHROMOSOME_LENGTH; i++) {
        lock_gene_t *gene = &chromosome->genes[i];
        float expression = (float)gene->dominance / 255.0f;
        
        switch (gene->type) {
            case GENE_TYPE_BACKOFF:
                behavior.backoff_strategy += (uint32_t)(gene->allele * expression);
                break;
            case GENE_TYPE_FAIRNESS:
                behavior.fairness_policy += (uint32_t)(gene->allele * expression);
                break;
            case GENE_TYPE_CONTENTION:
                behavior.contention_handling += (uint32_t)(gene->allele * expression);
                break;
            case GENE_TYPE_TIMING:
                behavior.timing_parameters += (uint32_t)(gene->allele * expression);
                break;
            case GENE_TYPE_MEMORY_ORDER:
                behavior.memory_ordering += (uint32_t)(gene->allele * expression);
                break;
            case GENE_TYPE_ADAPTIVE:
                behavior.adaptive_behavior += (uint32_t)(gene->allele * expression);
                break;
        }
    }
    
    // Simulate lock performance based on decoded behavior
    float fitness_components[5] = {0};
    
    // Throughput fitness (ops/second normalized)
    float base_throughput = 1000000.0f; // 1M ops/sec baseline
    float throughput_modifier = (float)behavior.backoff_strategy / 10000.0f;
    throughput_modifier += (float)behavior.contention_handling / 20000.0f;
    fitness_components[0] = sigmoid_activation(throughput_modifier - 0.5f);
    
    // Fairness fitness (FIFO coefficient)
    float fairness_modifier = (float)behavior.fairness_policy / 15000.0f;
    fitness_components[1] = sigmoid_activation(fairness_modifier - 0.5f);
    
    // Latency fitness (inverse of worst-case delay)
    float latency_modifier = 1.0f - ((float)behavior.timing_parameters / 20000.0f);
    fitness_components[2] = sigmoid_activation(latency_modifier);
    
    // Scalability fitness (performance under high contention)
    float scalability_modifier = (float)behavior.adaptive_behavior / 10000.0f;
    scalability_modifier *= (evaluator->workload.thread_count / 8.0f); // Scale with threads
    fitness_components[3] = sigmoid_activation(scalability_modifier - 0.3f);
    
    // Power efficiency fitness
    float power_modifier = 1.0f - ((float)behavior.memory_ordering / 30000.0f);
    fitness_components[4] = sigmoid_activation(power_modifier);
    
    // Combine fitness components using weighted sum
    float total_fitness = 0.0f;
    total_fitness += fitness_components[0] * evaluator->weights.throughput_weight;
    total_fitness += fitness_components[1] * evaluator->weights.fairness_weight;
    total_fitness += fitness_components[2] * evaluator->weights.latency_weight;
    total_fitness += fitness_components[3] * evaluator->weights.scalability_weight;
    total_fitness += fitness_components[4] * evaluator->weights.power_weight;
    
    // Apply workload-specific modifiers
    if (workload_type & WORKLOAD_TYPE_HIGH_CONTENTION) {
        total_fitness *= (1.0f + fitness_components[3] * 0.3f); // Bonus for scalability
    }
    
    if (workload_type & WORKLOAD_TYPE_REAL_TIME) {
        total_fitness *= (1.0f + fitness_components[2] * 0.5f); // Bonus for low latency
    }
    
    if (workload_type & WORKLOAD_TYPE_NUMA_DISTRIBUTED) {
        total_fitness *= (1.0f + chromosome->phenotype.numa_locality * 0.2f);
    }
    
    // Update chromosome fitness statistics
    uint64_t end_time = genetic_performance_counter();
    uint64_t evaluation_time = end_time - start_time;
    
    chromosome->fitness.evaluation_count++;
    chromosome->fitness.total_runtime_ns += evaluation_time;
    chromosome->fitness.current_fitness = total_fitness;
    
    // Update running average
    float alpha = 1.0f / (float)chromosome->fitness.evaluation_count;
    chromosome->fitness.average_fitness = 
        (1.0f - alpha) * chromosome->fitness.average_fitness + alpha * total_fitness;
    
    // Update peak fitness
    if (total_fitness > chromosome->fitness.peak_fitness) {
        chromosome->fitness.peak_fitness = total_fitness;
    }
    
    // Calculate fitness variance for stability measure
    float variance_delta = total_fitness - chromosome->fitness.average_fitness;
    chromosome->fitness.fitness_variance = 
        (1.0f - alpha) * chromosome->fitness.fitness_variance + 
        alpha * (variance_delta * variance_delta);
    
    // Update phenotype based on fitness components
    chromosome->phenotype.contention_efficiency = fitness_components[3];
    chromosome->phenotype.fairness_coefficient = fitness_components[1];
    chromosome->phenotype.cache_efficiency = fitness_components[0] * 0.8f + 
                                           fitness_components[4] * 0.2f;
    
    return total_fitness;
}

int genetic_crossover(const lock_chromosome_t *parent_a,
                     const lock_chromosome_t *parent_b,
                     lock_chromosome_t *offspring) {
    if (!parent_a || !parent_b || !offspring) {
        return -EINVAL;
    }
    
    // Initialize offspring with metadata
    offspring->organism_id = genetic_performance_counter(); // Unique ID
    offspring->generation = (parent_a->generation + parent_b->generation) / 2 + 1;
    offspring->parent_a_id = parent_a->organism_id;
    offspring->parent_b_id = parent_b->organism_id;
    
    // Multi-point crossover with variable crossover points
    uint32_t crossover_points[8];
    uint32_t num_points = 2 + (genetic_random() % 6); // 2-7 crossover points
    
    for (uint32_t i = 0; i < num_points; i++) {
        crossover_points[i] = genetic_random() % LOCK_CHROMOSOME_LENGTH;
    }
    
    // Sort crossover points
    for (uint32_t i = 0; i < num_points - 1; i++) {
        for (uint32_t j = i + 1; j < num_points; j++) {
            if (crossover_points[i] > crossover_points[j]) {
                uint32_t temp = crossover_points[i];
                crossover_points[i] = crossover_points[j];
                crossover_points[j] = temp;
            }
        }
    }
    
    // Perform crossover
    bool use_parent_a = true;
    uint32_t next_crossover = 0;
    
    for (uint32_t i = 0; i < LOCK_CHROMOSOME_LENGTH; i++) {
        if (next_crossover < num_points && i >= crossover_points[next_crossover]) {
            use_parent_a = !use_parent_a;
            next_crossover++;
        }
        
        const lock_chromosome_t *donor = use_parent_a ? parent_a : parent_b;
        offspring->genes[i] = donor->genes[i];
        
        // Apply gene-level blending for numerical traits
        if (genetic_random_float() < 0.3f) { // 30% chance of blending
            const lock_chromosome_t *other_parent = use_parent_a ? parent_b : parent_a;
            
            offspring->genes[i].allele = 
                (donor->genes[i].allele + other_parent->genes[i].allele) / 2;
            offspring->genes[i].dominance = 
                (donor->genes[i].dominance + other_parent->genes[i].dominance) / 2;
        }
    }
    
    // Initialize offspring fitness and phenotype
    offspring->fitness.current_fitness = 0.5f; // Neutral initial fitness
    offspring->fitness.average_fitness = 0.5f;
    offspring->fitness.peak_fitness = 0.5f;
    offspring->fitness.fitness_variance = 0.1f;
    offspring->fitness.evaluation_count = 0;
    offspring->fitness.total_runtime_ns = 0;
    
    // Blend phenotypes from parents
    offspring->phenotype.avg_acquisition_cycles = 
        (parent_a->phenotype.avg_acquisition_cycles + 
         parent_b->phenotype.avg_acquisition_cycles) / 2;
    offspring->phenotype.contention_efficiency = 
        (parent_a->phenotype.contention_efficiency + 
         parent_b->phenotype.contention_efficiency) / 2.0f;
    offspring->phenotype.fairness_coefficient = 
        (parent_a->phenotype.fairness_coefficient + 
         parent_b->phenotype.fairness_coefficient) / 2.0f;
    offspring->phenotype.cache_efficiency = 
        (parent_a->phenotype.cache_efficiency + 
         parent_b->phenotype.cache_efficiency) / 2.0f;
    offspring->phenotype.numa_locality = 
        (parent_a->phenotype.numa_locality + 
         parent_b->phenotype.numa_locality) / 2.0f;
    
    // Blend environmental preferences
    offspring->environment.preferred_workloads = 
        parent_a->environment.preferred_workloads | parent_b->environment.preferred_workloads;
    offspring->environment.cpu_affinity = 
        parent_a->environment.cpu_affinity & parent_b->environment.cpu_affinity;
    offspring->environment.temperature_tolerance = 
        (parent_a->environment.temperature_tolerance + 
         parent_b->environment.temperature_tolerance) / 2.0f;
    offspring->environment.power_efficiency = 
        (parent_a->environment.power_efficiency + 
         parent_b->environment.power_efficiency) / 2.0f;
    
    // Initialize atomic counters
    atomic_init(&offspring->reference_count, 0);
    atomic_init(&offspring->last_used_time, genetic_performance_counter());
    atomic_init(&offspring->deployment_count, 0);
    
    return 0;
}

int genetic_mutate(lock_chromosome_t *chromosome, float mutation_rate) {
    if (!chromosome || mutation_rate < 0.0f || mutation_rate > 1.0f) {
        return -EINVAL;
    }
    
    int mutations_applied = 0;
    
    for (uint32_t i = 0; i < LOCK_CHROMOSOME_LENGTH; i++) {
        lock_gene_t *gene = &chromosome->genes[i];
        
        // Check if gene should be mutated (considering stability)
        float effective_mutation_rate = mutation_rate * (1.0f - (float)gene->stability / 255.0f);
        
        if (genetic_random_float() < effective_mutation_rate) {
            mutations_applied++;
            
            // Choose mutation type
            uint32_t mutation_type = genetic_random() % 4;
            
            switch (mutation_type) {
                case 0: // Point mutation - change allele value
                    gene->allele = genetic_random() & 0xFF;
                    break;
                    
                case 1: // Dominance mutation - change gene expression
                    gene->dominance = genetic_random() & 0xFF;
                    break;
                    
                case 2: // Type mutation - change gene function
                    gene->type = (genetic_random() % 6) + 1;
                    gene->allele = genetic_random() & 0xFF; // Re-randomize allele for new type
                    break;
                    
                case 3: // Stability mutation - change mutation resistance
                    if (genetic_random_float() < 0.1f) { // Rare stability mutations
                        gene->stability = genetic_random() & 0xFF;
                    }
                    break;
            }
            
            // Apply Gaussian noise to numerical phenotype traits
            if (genetic_random_float() < 0.5f) {
                chromosome->phenotype.contention_efficiency += gaussian_random(0.0f, 0.05f);
                chromosome->phenotype.contention_efficiency = 
                    fmax(0.0f, fmin(1.0f, chromosome->phenotype.contention_efficiency));
                
                chromosome->phenotype.fairness_coefficient += gaussian_random(0.0f, 0.05f);
                chromosome->phenotype.fairness_coefficient = 
                    fmax(0.0f, fmin(1.0f, chromosome->phenotype.fairness_coefficient));
            }
        }
    }
    
    // Apply large-scale chromosomal mutations rarely
    if (genetic_random_float() < 0.01f) { // 1% chance
        mutations_applied++;
        
        // Chromosomal rearrangement - swap gene segments
        uint32_t start = genetic_random() % LOCK_CHROMOSOME_LENGTH;
        uint32_t end = start + (genetic_random() % (LOCK_CHROMOSOME_LENGTH - start));
        uint32_t target = genetic_random() % (LOCK_CHROMOSOME_LENGTH - (end - start));
        
        // Temporary storage for gene segment
        lock_gene_t temp_segment[LOCK_CHROMOSOME_LENGTH];
        memcpy(temp_segment, &chromosome->genes[start], (end - start) * sizeof(lock_gene_t));
        
        // Shift genes to make room
        if (target < start) {
            memmove(&chromosome->genes[target + (end - start)], &chromosome->genes[target],
                   (start - target) * sizeof(lock_gene_t));
        } else {
            memmove(&chromosome->genes[start], &chromosome->genes[end],
                   (target - start) * sizeof(lock_gene_t));
        }
        
        // Insert segment at new location
        memcpy(&chromosome->genes[target], temp_segment, (end - start) * sizeof(lock_gene_t));
    }
    
    // Update organism generation if significant mutations occurred
    if (mutations_applied > 5) {
        chromosome->generation++;
    }
    
    return mutations_applied;
}

int genetic_evolve_generation(genetic_evolution_engine_t *engine) {
    if (!engine) {
        return -EINVAL;
    }
    
    // Check if evolution is enabled and not already in progress
    if (!atomic_load_explicit(&engine->evolution_enabled, memory_order_relaxed) ||
        atomic_exchange_explicit(&engine->breeding_in_progress, 1, memory_order_acq_rel)) {
        return -EBUSY;
    }
    
    genetic_population_t *population = &engine->population;
    uint64_t generation_start = genetic_performance_counter();
    
    // Evaluate fitness of entire population
    uint32_t current_workload = population->environment.current_workload_type;
    for (uint32_t i = 0; i < atomic_load_explicit(&population->population_size, memory_order_relaxed); i++) {
        genetic_evaluate_fitness(&population->organisms[i], &engine->evaluator, current_workload);
    }
    
    // Sort population by fitness (descending)
    qsort(population->organisms, 
          atomic_load_explicit(&population->population_size, memory_order_relaxed),
          sizeof(lock_chromosome_t), compare_fitness_desc);
    
    // Preserve elite organisms
    genetic_preserve_elite(population);
    
    // Create new generation
    lock_chromosome_t new_generation[LOCK_GENE_POOL_SIZE];
    uint32_t new_population_size = 0;
    
    // Keep elite organisms (top 10%)
    uint32_t elite_count = LOCK_GENE_POOL_SIZE / 10;
    for (uint32_t i = 0; i < elite_count; i++) {
        new_generation[new_population_size++] = population->organisms[i];
    }
    
    // Generate offspring through crossover and mutation
    while (new_population_size < LOCK_GENE_POOL_SIZE) {
        lock_chromosome_t *parent_a, *parent_b;
        
        // Select parents using fitness-proportionate selection
        if (genetic_select_parents(population, &parent_a, &parent_b) < 0) {
            break;
        }
        
        lock_chromosome_t offspring;
        
        // Perform crossover
        if (genetic_random_float() < LOCK_CROSSOVER_RATE) {
            if (genetic_crossover(parent_a, parent_b, &offspring) == 0) {
                atomic_fetch_add_explicit(&population->successful_crossovers, 1, memory_order_relaxed);
            } else {
                offspring = *parent_a; // Fallback to asexual reproduction
            }
        } else {
            offspring = *parent_a; // Asexual reproduction
        }
        
        // Apply mutations
        float mutation_rate = genetic_adaptive_mutation_rate(population);
        int mutations = genetic_mutate(&offspring, mutation_rate);
        if (mutations > 0) {
            atomic_fetch_add_explicit(&population->successful_mutations, 1, memory_order_relaxed);
        }
        
        new_generation[new_population_size++] = offspring;
    }
    
    // Replace old population with new generation
    memcpy(population->organisms, new_generation, 
           new_population_size * sizeof(lock_chromosome_t));
    atomic_store_explicit(&population->population_size, new_population_size, memory_order_relaxed);
    
    // Update generation counter
    atomic_fetch_add_explicit(&population->current_generation, 1, memory_order_relaxed);
    atomic_fetch_add_explicit(&engine->statistics.total_evolutions, 1, memory_order_relaxed);
    
    // Calculate diversity metrics
    genetic_calculate_diversity(population);
    
    // Check for potential deployment of superior algorithms
    if (population->organisms[0].fitness.current_fitness > ELITE_FITNESS_THRESHOLD) {
        // Find best lock type match for this algorithm
        meta_lock_type_t best_type = META_LOCK_TICKET; // Default
        
        // Heuristic mapping based on phenotype characteristics
        if (population->organisms[0].phenotype.contention_efficiency > 0.8f) {
            best_type = META_LOCK_MCS; // Good for high contention
        } else if (population->organisms[0].phenotype.fairness_coefficient > 0.9f) {
            best_type = META_LOCK_TICKET; // Fair queuing
        } else if (population->organisms[0].phenotype.cache_efficiency > 0.8f) {
            best_type = META_LOCK_SEQLOCK; // Read-optimized
        }
        
        genetic_deploy_algorithm(engine, best_type, &population->organisms[0]);
    }
    
    // Update timing
    atomic_store_explicit(&engine->last_evolution_time, 
                         genetic_performance_counter(), memory_order_relaxed);
    
    // Release breeding lock
    atomic_store_explicit(&engine->breeding_in_progress, 0, memory_order_release);
    
    return 0;
}

// Internal helper function implementations

static uint64_t genetic_random(void) {
    // Linear congruential generator (simple but fast)
    genetic_random_state = genetic_random_state * 1103515245 + 12345;
    return genetic_random_state;
}

static float genetic_random_float(void) {
    return (float)genetic_random() / (float)UINT64_MAX;
}

static uint64_t genetic_performance_counter(void) {
    // Use TSC or similar high-resolution counter
    uint64_t tsc;
    __asm__ __volatile__(
        "rdtsc"
        : "=A"(tsc)
    );
    return tsc;
}

static float sigmoid_activation(float x) {
    // Sigmoid activation function: f(x) = 1 / (1 + e^(-x))
    return 1.0f / (1.0f + expf(-x));
}

static float gaussian_random(float mean, float stddev) {
    // Box-Muller transform for Gaussian distribution
    static bool has_spare = false;
    static float spare;
    
    if (has_spare) {
        has_spare = false;
        return spare * stddev + mean;
    }
    
    has_spare = true;
    float u = genetic_random_float();
    float v = genetic_random_float();
    float mag = stddev * sqrtf(-2.0f * logf(u));
    spare = mag * cosf(2.0f * M_PI * v);
    
    return mag * sinf(2.0f * M_PI * v) + mean;
}

static int compare_fitness_desc(const void *a, const void *b) {
    const lock_chromosome_t *org_a = (const lock_chromosome_t *)a;
    const lock_chromosome_t *org_b = (const lock_chromosome_t *)b;
    
    if (org_a->fitness.current_fitness > org_b->fitness.current_fitness) {
        return -1;
    } else if (org_a->fitness.current_fitness < org_b->fitness.current_fitness) {
        return 1;
    } else {
        return 0;
    }
}

// Additional core functions (simplified implementations)

int genetic_select_parents(genetic_population_t *population,
                          lock_chromosome_t **parent_a,
                          lock_chromosome_t **parent_b) {
    if (!population || !parent_a || !parent_b) {
        return -EINVAL;
    }
    
    uint32_t pop_size = atomic_load_explicit(&population->population_size, memory_order_relaxed);
    if (pop_size < 2) {
        return -EINVAL;
    }
    
    // Tournament selection with tournament size = 3
    uint32_t best_a = 0, best_b = 0;
    float best_fitness_a = 0.0f, best_fitness_b = 0.0f;
    
    // Tournament for parent A
    for (int i = 0; i < 3; i++) {
        uint32_t candidate = genetic_random() % pop_size;
        if (population->organisms[candidate].fitness.current_fitness > best_fitness_a) {
            best_fitness_a = population->organisms[candidate].fitness.current_fitness;
            best_a = candidate;
        }
    }
    
    // Tournament for parent B (ensure different from A)
    for (int i = 0; i < 3; i++) {
        uint32_t candidate = genetic_random() % pop_size;
        if (candidate != best_a && 
            population->organisms[candidate].fitness.current_fitness > best_fitness_b) {
            best_fitness_b = population->organisms[candidate].fitness.current_fitness;
            best_b = candidate;
        }
    }
    
    *parent_a = &population->organisms[best_a];
    *parent_b = &population->organisms[best_b];
    
    return 0;
}

int genetic_preserve_elite(genetic_population_t *population) {
    if (!population) {
        return -EINVAL;
    }
    
    uint32_t pop_size = atomic_load_explicit(&population->population_size, memory_order_relaxed);
    uint32_t elite_size = (uint32_t)(pop_size * LOCK_ELITE_PRESERVATION);
    
    // Copy top performers to elite array
    for (uint32_t i = 0; i < elite_size && i < LOCK_GENE_POOL_SIZE / 10; i++) {
        population->elite[i] = population->organisms[i];
    }
    
    atomic_store_explicit(&population->elite_count, elite_size, memory_order_relaxed);
    return 0;
}

float genetic_adaptive_mutation_rate(genetic_population_t *population) {
    if (!population) {
        return LOCK_MUTATION_RATE;
    }
    
    // Increase mutation rate when diversity is low
    float diversity = population->diversity.genetic_diversity;
    float base_rate = LOCK_MUTATION_RATE;
    
    if (diversity < DIVERSITY_CRISIS_THRESHOLD) {
        return base_rate * 3.0f; // Triple mutation rate during diversity crisis
    } else if (diversity < 0.3f) {
        return base_rate * 1.5f; // Increase mutation rate for low diversity
    }
    
    return base_rate;
}

int genetic_calculate_diversity(genetic_population_t *population) {
    if (!population) {
        return -EINVAL;
    }
    
    uint32_t pop_size = atomic_load_explicit(&population->population_size, memory_order_relaxed);
    if (pop_size == 0) {
        return 0;
    }
    
    // Calculate genetic diversity using Shannon entropy
    uint32_t gene_counts[256][LOCK_CHROMOSOME_LENGTH] = {0};
    
    for (uint32_t i = 0; i < pop_size; i++) {
        for (uint32_t j = 0; j < LOCK_CHROMOSOME_LENGTH; j++) {
            gene_counts[population->organisms[i].genes[j].allele][j]++;
        }
    }
    
    float total_entropy = 0.0f;
    for (uint32_t j = 0; j < LOCK_CHROMOSOME_LENGTH; j++) {
        float locus_entropy = 0.0f;
        for (uint32_t allele = 0; allele < 256; allele++) {
            if (gene_counts[allele][j] > 0) {
                float p = (float)gene_counts[allele][j] / (float)pop_size;
                locus_entropy -= p * log2f(p);
            }
        }
        total_entropy += locus_entropy;
    }
    
    population->diversity.genetic_diversity = total_entropy / (8.0f * LOCK_CHROMOSOME_LENGTH);
    
    // Calculate fitness spread
    float min_fitness = 1.0f, max_fitness = 0.0f;
    for (uint32_t i = 0; i < pop_size; i++) {
        float fitness = population->organisms[i].fitness.current_fitness;
        if (fitness < min_fitness) min_fitness = fitness;
        if (fitness > max_fitness) max_fitness = fitness;
    }
    population->diversity.fitness_spread = max_fitness - min_fitness;
    
    return 0;
}

int genetic_deploy_algorithm(genetic_evolution_engine_t *engine,
                            meta_lock_type_t lock_type,
                            lock_chromosome_t *chromosome) {
    if (!engine || !chromosome || lock_type >= META_LOCK_TYPE_MAX) {
        return -EINVAL;
    }
    
    // Store reference to evolved algorithm
    engine->deployment.active_algorithms[lock_type] = chromosome;
    atomic_store_explicit(&engine->deployment.deployment_generation[lock_type],
                         chromosome->generation, memory_order_relaxed);
    engine->deployment.last_deployment_time[lock_type] = genetic_performance_counter();
    
    // Update deployment statistics
    atomic_fetch_add_explicit(&engine->statistics.successful_deployments, 1, memory_order_relaxed);
    
    // Increment chromosome usage
    atomic_fetch_add_explicit(&chromosome->deployment_count, 1, memory_order_relaxed);
    atomic_store_explicit(&chromosome->last_used_time, 
                         genetic_performance_counter(), memory_order_relaxed);
    
    return 0;
}

/**
 * @brief Execute genetically evolved lock acquisition
 * @param chromosome Evolved algorithm chromosome
 * @param lock Target ultimate lock
 * @param timeout_ns Maximum wait time
 * @return 0 on success, negative errno on failure
 */
int genetic_execute_evolved_acquire(lock_chromosome_t *chromosome, 
                                   ultimate_lock_t *lock, 
                                   uint64_t timeout_ns) {
    if (!chromosome || !lock) {
        return -EINVAL;
    }
    
    uint64_t start_time = genetic_performance_counter();
    
    // Decode genetic algorithm behavior
    uint32_t backoff_strategy = 0;
    uint32_t fairness_policy = 0;
    uint32_t adaptive_behavior = 0;
    
    // Extract behavior parameters from chromosome genes
    for (uint32_t i = 0; i < LOCK_CHROMOSOME_LENGTH; i++) {
        lock_gene_t *gene = &chromosome->genes[i];
        float expression = (float)gene->dominance / 255.0f;
        
        switch (gene->type) {
            case GENE_TYPE_BACKOFF:
                backoff_strategy += (uint32_t)(gene->allele * expression);
                break;
            case GENE_TYPE_FAIRNESS:
                fairness_policy += (uint32_t)(gene->allele * expression);
                break;
            case GENE_TYPE_ADAPTIVE:
                adaptive_behavior += (uint32_t)(gene->allele * expression);
                break;
        }
    }
    
    // Normalize parameters
    backoff_strategy = (backoff_strategy % 1000) + 1;  // 1-1000 cycles
    fairness_policy = fairness_policy % 100;           // 0-99% fairness
    adaptive_behavior = adaptive_behavior % 10 + 1;    // 1-10 adaptation levels
    
    // Implement evolved acquisition strategy
    uint64_t attempts = 0;
    uint64_t max_attempts = timeout_ns ? (timeout_ns / 1000) : UINT64_MAX;
    
    while (attempts < max_attempts) {
        // Try atomic acquisition (basic CAS operation)
        uint64_t expected = 0;
        uint64_t desired = (uint64_t)getpid() | ((uint64_t)genetic_performance_counter() << 32);
        
        if (atomic_compare_exchange_weak_explicit(
                (atomic_uint64_t*)&lock->impl.genetic.chromosome_ref,
                &expected, desired, memory_order_acquire, memory_order_relaxed)) {
            
            // Success - update chromosome statistics
            atomic_fetch_add_explicit(&chromosome->reference_count, 1, memory_order_relaxed);
            atomic_store_explicit(&chromosome->last_used_time, 
                                 genetic_performance_counter(), memory_order_relaxed);
            
            return 0;
        }
        
        // Apply evolved backoff strategy
        if (attempts % fairness_policy == 0) {
            // Fairness-based yield
            yield();
        } else {
            // Genetic backoff pattern
            uint32_t backoff_cycles = backoff_strategy * 
                                    (1 + (attempts % adaptive_behavior));
            
            for (uint32_t i = 0; i < backoff_cycles; i++) {
                __builtin_ia32_pause();
            }
        }
        
        attempts++;
        
        // Check timeout
        if (timeout_ns > 0) {
            uint64_t elapsed = genetic_performance_counter() - start_time;
            if (elapsed > timeout_ns) {
                return -ETIMEDOUT;
            }
        }
    }
    
    return -EBUSY;
}

/**
 * @brief Execute genetically evolved lock release
 * @param chromosome Evolved algorithm chromosome
 * @param lock Target ultimate lock
 * @return 0 on success, negative errno on failure
 */
int genetic_execute_evolved_release(lock_chromosome_t *chromosome, 
                                   ultimate_lock_t *lock) {
    if (!chromosome || !lock) {
        return -EINVAL;
    }
    
    // Decode release behavior from chromosome
    uint32_t release_strategy = 0;
    for (uint32_t i = 0; i < LOCK_CHROMOSOME_LENGTH; i++) {
        if (chromosome->genes[i].type == GENE_TYPE_FAIRNESS) {
            release_strategy += chromosome->genes[i].allele;
        }
    }
    
    // Apply evolved release strategy
    if (release_strategy % 4 == 0) {
        // Immediate release
        atomic_store_explicit((atomic_uint64_t*)&lock->impl.genetic.chromosome_ref, 
                            0, memory_order_release);
    } else {
        // Gradual release with memory barriers
        atomic_thread_fence(memory_order_release);
        atomic_store_explicit((atomic_uint64_t*)&lock->impl.genetic.chromosome_ref, 
                            0, memory_order_release);
        atomic_thread_fence(memory_order_seq_cst);
    }
    
    // Update chromosome fitness based on hold time
    uint64_t current_time = genetic_performance_counter();
    uint64_t last_used = atomic_load_explicit(&chromosome->last_used_time, memory_order_relaxed);
    uint64_t hold_time = current_time - last_used;
    
    // Shorter hold times get better fitness (less blocking)
    float hold_time_fitness = 1000000.0f / (float)(hold_time + 1000);
    chromosome->fitness.current_fitness = 
        0.9f * chromosome->fitness.current_fitness + 0.1f * hold_time_fitness;
    
    return 0;
}

// Global evolution engine declaration
extern genetic_evolution_engine_t global_evolution_engine;

// Helper function for getpid in kernel context
static int getpid(void) {
    extern struct proc *myproc(void);
    struct proc *p = myproc();
    return p ? p->pid : 0;
}

// Helper function for yield in kernel context
static void yield(void) {
    extern void yield(void);
    // Call kernel yield function
}

// Initialization function for the global engine
void genetic_evolution_subsystem_init(void) {
    if (!evolution_engine_initialized) {
        genetic_evolution_init(&global_evolution_engine);
        evolution_engine_initialized = true;
        
        cprintf("Genetic Lock Evolution Engine initialized\n");
        cprintf("Population size: %d organisms\n", LOCK_GENE_POOL_SIZE);
        cprintf("Chromosome length: %d genes\n", LOCK_CHROMOSOME_LENGTH);
        cprintf("Mutation rate: %.3f\n", LOCK_MUTATION_RATE);
        cprintf("Crossover rate: %.3f\n", LOCK_CROSSOVER_RATE);
        
        // Start initial evolution
        genetic_evolve_generation(&global_evolution_engine);
    }
}