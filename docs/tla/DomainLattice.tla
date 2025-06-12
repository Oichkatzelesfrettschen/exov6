--------------------------- MODULE DomainLattice ---------------------------
EXTENDS Naturals, FiniteSets, TLC

CONSTANTS
    Domains,
    RootDomain,
    NullDomain,
    MaxClsLevel,
    AllCats

ASSUME /\ RootDomain \in Domains
       /\ NullDomain \in Domains
       /\ RootDomain /= NullDomain
       /\ Cardinality(Domains) >= 2

VARIABLES
    domainLattice

TypeOK_DomainLattice ==
    /\ domainLattice \in [Domains -> [cls: 0..MaxClsLevel, cats: SUBSET AllCats]]
    /\ domainLattice[RootDomain] = [cls |-> MaxClsLevel, cats |-> AllCats]
    /\ domainLattice[NullDomain] = [cls |-> 0, cats |-> {}]

LatticeLeq(level_d1, level_d2) ==
    /\ level_d1.cls <= level_d2.cls
    /\ level_d1.cats \subseteq level_d2.cats

=============================================================================
