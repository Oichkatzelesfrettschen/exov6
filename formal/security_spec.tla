---------------- MODULE security_spec ----------------
EXTENDS Naturals

CONSTANTS
    Process,      \* Set of processes
    Resource      \* Set of resources

VARIABLES
    owner,        \* Resource -> Process (fixed owner)
    access        \* Resource -> Set(Process) (who has capability)

Init ==
    /\ owner \in [Resource -> Process]
    /\ access = [r \in Resource |-> {owner[r]}] \* Initially only owner has access

\* Grant access (capability transfer)
Grant(p, q, r) ==
    /\ p \in access[r]      \* p has access (can delegate)
    /\ access' = [access EXCEPT ![r] = @ \cup {q}]
    /\ UNCHANGED owner

\* Revoke access (owner only)
Revoke(p, r) ==
    /\ owner[r] = p
    /\ access' = [access EXCEPT ![r] = {p}]
    /\ UNCHANGED owner

Next ==
    \E p, q \in Process, r \in Resource :
        \/ Grant(p, q, r)
        \/ Revoke(p, r)

\* Invariant: Owner always has access
OwnerAccessInv ==
    \A r \in Resource : owner[r] \in access[r]

Spec == Init /\ [][Next]_<<owner, access>>

THEOREM Spec => []OwnerAccessInv
======================================================
