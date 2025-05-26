---- MODULE ExoCap ----
EXTENDS Naturals, TLC

VARIABLES cid, rights, owner, tag

ComputeTag(id, r, o) == id + r + o

Init == /\ cid \in Nat
        /\ rights \in Nat
        /\ owner \in Nat
        /\ tag = ComputeTag(cid, rights, owner)

HasRights(r, need) == (r /\ need) = need
Verify == ComputeTag(cid, rights, owner) = tag

Next == UNCHANGED <<cid, rights, owner, tag>>

Spec == Init /\ [][Next]_<<cid, rights, owner, tag>>

Inv == Verify

THEOREM Inv => []Inv
=============================================================================
