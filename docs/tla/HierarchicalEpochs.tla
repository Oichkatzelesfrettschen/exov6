-------------------------- MODULE HierarchicalEpochs --------------------------
EXTENDS DomainLattice, DelegationAlgebra, VectorTimestamps, Naturals, FiniteSets, Sequences, TLC

ASSUME NumDomains = Cardinality(Domains)

VARIABLES
    domainLattice,    \* From DomainLattice: function d \in Domains |-> SecurityLevel record
    domainEpochs,     \* Function d \in Domains |-> Nat (current epoch of the domain)
    capabilities,     \* Set of Capability records (defined in DelegationAlgebra)
    nextCapId,        \* Next available capability ID
    vts               \* Function d \in Domains |-> VectorTimestamp (per-domain vector timestamps)

\* Helper to map domain ID to a VT index (0 to NumDomains-1)
DomainsAsSeq == CHOOSE S \in Seq(Domains) : IsPermutation(S, Domains)
VT_IndexOf(d) == CHOOSE i \in 0..(NumDomains-1) : DomainsAsSeq[i+1] = d

TypeOK ==
    /\ TypeOK_DomainLattice \* From DomainLattice.tla
    /\ TypeOK_Capabilities  \* From DelegationAlgebra.tla (checks 'capabilities', 'nextCapId')
    /\ domainEpochs \in [Domains -> Nat]
    /\ Assert(NumDomains > 0, "NumDomains must be positive for VT_IndexOf")
    /\ \A d \in Domains : VT_IndexOf(d) \in 0..(NumDomains-1) \* Ensure VT_IndexOf is well-defined for all domains
    /\ vts \in [Domains -> [0..(NumDomains-1) -> Nat]]
    /\ \A d \in Domains : IsVectorTimestamp(vts[d]) \* IsVectorTimestamp from VectorTimestamps.tla

Init ==
    /\ Init_DomainLattice  \* From DomainLattice.tla
    /\ Init_Capabilities   \* From DelegationAlgebra.tla (inits 'capabilities', 'nextCapId')
    /\ domainEpochs = [d \in Domains |-> 0]
    /\ vts = [d \in Domains |-> VTInitComplete(NumDomains)] \* VTInitComplete from VectorTimestamps.tla

CreateCapability(ownerDom, newRights) ==
    /\ ownerDom \in Domains
    /\ newRights \subseteq AllRights
    /\ Action_CreateCapability(ownerDom, newRights, domainEpochs[ownerDom]) \* Uses 'capabilities', 'nextCapId'
    /\ vts' = [d \in Domains |-> IF d = ownerDom THEN VTLocalEvent(vts[ownerDom], VT_IndexOf(ownerDom)) ELSE vts[d]]
    /\ UNCHANGED <<domainLattice, domainEpochs>>

DelegateCapability(capIdToDelegate, delegatorDom, targetDom, rightsMask) ==
    /\ delegatorDom \in Domains
    /\ targetDom \in Domains
    /\ rightsMask \subseteq AllRights
    /\ CanDelegate(domainLattice[delegatorDom], domainLattice[targetDom]) \* From DomainLattice.tla
    /\ Action_DelegateCapability(capIdToDelegate, delegatorDom, targetDom, rightsMask, domainEpochs[targetDom]) \* Uses 'capabilities', 'nextCapId'
    /\ vts' = [d \in Domains |-> IF d = delegatorDom THEN VTLocalEvent(vts[delegatorDom], VT_IndexOf(delegatorDom)) ELSE vts[d]]
    /\ UNCHANGED <<domainLattice, domainEpochs>>

AdvanceDomainEpoch(dom) ==
    /\ dom \in Domains
    /\ domainEpochs' = [domainEpochs EXCEPT ![dom] = @ + 1]
    /\ vts' = [d \in Domains |-> IF d = dom THEN VTLocalEvent(vts[dom], VT_IndexOf(dom)) ELSE vts[d]]
    /\ UNCHANGED <<domainLattice, capabilities, nextCapId>>

\* Represents a capability being checked/used.
\* If capEpoch < domainEpochs[capOwner], it's revoked.
\* This action doesn't change state but models a check.
CheckCapability(capId, requestingDom) ==
    /\ capId \in {c.id : c \in capabilities}
    /\ requestingDom \in Domains
    /\ LET cap == CHOOSE c \in capabilities : c.id = capId IN
        /\ IsRevoked(cap, domainEpochs[cap.owner]) = FALSE
        /\ CanAccess(domainLattice[requestingDom], domainLattice[cap.owner])
    /\ UNCHANGED <<domainLattice, domainEpochs, capabilities, nextCapId, vts>>

LearnOtherDomainState(learnerDom, sourceDom) ==
    /\ learnerDom \in Domains
    /\ sourceDom \in Domains
    /\ learnerDom /= sourceDom
    /\ vts' = [d \in Domains |->
                IF d = learnerDom THEN
                    VTLocalEvent(VTMerge(vts[learnerDom], vts[sourceDom]), VT_IndexOf(learnerDom))
                ELSE vts[d]]
    /\ UNCHANGED <<domainLattice, domainEpochs, capabilities, nextCapId>>

Next ==
    \/ \E owner \in Domains, r \in SUBSET AllRights : CreateCapability(owner, r)
    \/ \E cId \in {cap.id : c \in capabilities}, delegator \in Domains, target \in Domains, mask \in SUBSET AllRights:
        DelegateCapability(cId, delegator, target, mask)
    \/ \E d \in Domains : AdvanceDomainEpoch(d)
    \/ \E cId \in {cap.id : c \in capabilities}, reqDom \in Domains : CheckCapability(cId, reqDom)
    \/ \E learner \in Domains, source \in Domains : (learner /= source) /\ LearnOtherDomainState(learner, source)

vars == <<domainLattice, domainEpochs, capabilities, nextCapId, vts>>
Spec == Init /\ [][Next]_vars

------------------------------ THEOREMS AND INVARIANTS ------------------------------
\* Type invariant holds.
THEOREM TypeOkTheorem == Spec => []TypeOK

\* Epochs only increase or stay the same.
Invariant_EpochMonotonicity ==
    \A d \in Domains : domainEpochs'[d] >= domainEpochs[d]
THEOREM EpochMonotonicityTheorem == Spec => []Invariant_EpochMonotonicity

\* A delegated capability's rights are a subset of its parent's rights.
Invariant_DelegationRightsAttenuation ==
    \A new_cap \in capabilities' :
        IF new_cap
otin capabilities THEN \* If new_cap is truly new
            \E parent_cap_id \in {c.id : c \in capabilities}, delegator \in Domains, target \in Domains, mask \in SUBSET AllRights :
                /\ DelegateCapability(parent_cap_id, delegator, target, mask) \* This was the action
                /\ new_cap.owner = target
                /\ LET parent_cap == CHOOSE pc \in capabilities : pc.id = parent_cap_id AND pc.owner = delegator IN
                    new_cap.rights \subseteq parent_cap.rights
        ELSE TRUE
THEOREM DelegationRightsAttenuationTheorem == Spec => []Invariant_DelegationRightsAttenuation

\* Delegation respects lattice security ordering (CanDelegate).
Invariant_DelegationLatticeOrder ==
    \A cId \in {cap.id : c \in capabilities}, delegator \in Domains, target \in Domains, mask \in SUBSET AllRights:
        ENABLED DelegateCapability(cId, delegator, target, mask) => CanDelegate(domainLattice[delegator], domainLattice[target])
THEOREM DelegationLatticeOrderTheorem == Spec => []Invariant_DelegationLatticeOrder

\* Vector timestamp components are non-decreasing.
Invariant_VectorTimestampMonotonicity ==
    \A d \in Domains :
        /\ vts'[d][VT_IndexOf(d)] >= vts[d][VT_IndexOf(d)]
        /\ \A other_d \in Domains : d /= other_d => vts'[d][VT_IndexOf(other_d)] >= vts[d][VT_IndexOf(other_d)]
THEOREM VectorTimestampMonotonicityTheorem == Spec => []Invariant_VectorTimestampMonotonicity

\* Vector timestamp causality: if learner learns from source, learner's knowledge of source is updated.
Invariant_VectorTimestampCausality ==
    \A learner \in Domains, source \in Domains :
        learner /= source /\ ENABLED LearnOtherDomainState(learner, source) =>
            LET vtLearnerNext == vts'[learner]
                vtSourceAtSend == vts[source] \* Source's VT at the time of "sending"
            IN
            vtLearnerNext[VT_IndexOf(source)] >= vtSourceAtSend[VT_IndexOf(source)]
THEOREM VectorTimestampCausalityTheorem == Spec => []Invariant_VectorTimestampCausality

\* If a capability is used (CheckCapability), it must not be revoked.
Invariant_NoRevokedAccess ==
    \A capId \in {c.id : c \in capabilities}, reqDom \in Domains :
        ENABLED CheckCapability(capId, reqDom) =>
            LET cap == CHOOSE c \in capabilities : c.id = capId IN
            IsRevoked(cap, domainEpochs[cap.owner]) = FALSE
THEOREM NoRevokedAccessTheorem == Spec => []Invariant_NoRevokedAccess

\* Liveness: It's always possible for some domain to advance its epoch.
Liveness_EpochCanAdvance ==
    \A d \in Domains : <> \E d_advanced \in Domains : domainEpochs[d_advanced] > 0
    (* More robust: WF_vars(AdvanceDomainEpoch(d)) for some d *)
THEOREM EpochEventuallyAdvances == Spec => \A d \in Domains : <> (domainEpochs[d] > 0)
    (* This is a simplification. A better one would be that it's always possible to take an action that leads to an epoch advance.
       Or, for every state, there's a future state where some epoch is higher.
       A common liveness property: []( \E d \in Domains: ENABLED AdvanceDomainEpoch(d) )
       Or: \A d \in Domains : Init => <> (domainEpochs[d] > 0)
       This needs TLC to verify with fairness. For now, a simple reachability.
    *)

\* Liveness: It's always possible to create a capability (assuming nextCapId < CapMax).
Liveness_CapabilityCanBeCreated ==
    Init => <>(capabilities /= {})
    (* Stronger: [](nextCapId < CapMax => \E owner, rights: ENABLED CreateCapability(owner, rights)) *)
THEOREM CapabilityCreationPossible == Spec => <>(capabilities /= {})

=============================================================================