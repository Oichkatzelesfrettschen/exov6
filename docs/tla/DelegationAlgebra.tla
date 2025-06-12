----------------------- MODULE DelegationAlgebra -----------------------
EXTENDS DomainLattice, Naturals, FiniteSets, TLC

CONSTANTS
    AllRights,
    CapMax

VARIABLES
    capabilities,
    nextCapId

TypeOK_Capabilities ==
    /\ ({ cap \in capabilities :
           /\ cap.id \in 0..(CapMax-1)
           /\ cap.rights \subseteq AllRights
           /\ cap.owner \in Domains       \* Domains is from DomainLattice
           /\ cap.cEpoch \in Nat
       } = capabilities) \* Ensures all capabilities in the set conform
    /\ nextCapId \in 0..CapMax

CanDelegate(capOwnerDomainID, targetDomainID) ==
    LatticeLeq(domainLattice[targetDomainID], domainLattice[capOwnerDomainID]) \* domainLattice from DomainLattice

AttenuateRights(parentRights, rightsMask) ==
    parentRights \intersect rightsMask

=============================================================================
