---- MODULE Capability ----
EXTENDS Naturals, TLC

CONSTANT Users

VARIABLES caps, owner, active

Init == /\ caps = {}
         /\ owner = [c \in {} |-> 0]
         /\ active = NULL

Create(c,u) == /\ c \notin caps
                /\ caps' = caps \cup {c}
                /\ owner' = [owner EXCEPT ![c] = u]
                /\ UNCHANGED active

Revoke(c,u) == /\ c \in caps
                /\ owner[c] = u
                /\ caps' = caps \ {c}
                /\ owner' = [o \in DOMAIN owner \ {c} |-> owner[o]]
                /\ active' = IF active = c THEN NULL ELSE active

YieldTo(src,dst,u) == /\ src \in caps
                     /\ dst \in caps
                     /\ owner[src] = u
                     /\ active = src
                     /\ active' = dst
                     /\ UNCHANGED <<caps, owner>>

Next == \E c \in Nat, u \in Users : Create(c,u)
        \/ \E c \in caps, u \in Users : Revoke(c,u)
        \/ \E s \in caps, d \in caps, u \in Users : YieldTo(s,d,u)

Spec == Init /\ [][Next]_<<caps,owner,active>>

ActiveInv == active = NULL \/ active \in caps

====
