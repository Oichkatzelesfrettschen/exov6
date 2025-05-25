----------------------------- MODULE CapabilityLifecycle -----------------------------
EXTENDS Naturals, Sequences

CONSTANT Caps

VARIABLES state, owner, requests

CapStates == {"free", "active", "revoked"}

Init == /\ state = [c \in Caps |-> "free"]
        /\ owner = [c \in Caps |-> 0]
        /\ requests = <<>>

Create(c, o) == /\ state[c] = "free"
                /\ state' = [state EXCEPT ![c] = "active"]
                /\ owner' = [owner EXCEPT ![c] = o]
                /\ UNCHANGED requests

Revoke(c) == /\ state[c] = "active"
             /\ state' = [state EXCEPT ![c] = "revoked"]
             /\ UNCHANGED <<owner, requests>>

Verify(c) == /\ state[c] = "active"
             /\ UNCHANGED <<state, owner, requests>>

Request(c) == requests' = Append(requests, c) /\ UNCHANGED <<state, owner>>

Grant == /\ requests # <<>>
         /\ LET c == Head(requests) IN state[c] = "active"
         /\ requests' = Tail(requests)
         /\ UNCHANGED <<state, owner>>

Next == \E c \in Caps, o \in Nat : Create(c, o)
        \/ \E c \in Caps : Revoke(c)
        \/ \E c \in Caps : Verify(c)
        \/ \E c \in Caps : Request(c)
        \/ Grant

Spec == Init /\ [][Next]_<<state, owner, requests>>

=============================================================================
