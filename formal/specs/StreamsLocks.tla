---- MODULE StreamsLocks ----
EXTENDS TLC

Proc == {"stream", "rpc"}

VARIABLES spinlock, qspinlock, pc

Init == /\ spinlock = "free"
         /\ qspinlock = "free"
         /\ pc = [p \in Proc |-> "start"]

(* STREAMS handler steps *)
StreamAcquireSpin ==
    /\ pc["stream"] = "start"
    /\ spinlock = "free"
    /\ spinlock' = "stream"
    /\ pc' = [pc EXCEPT !["stream"] = "got_spin"]
    /\ UNCHANGED qspinlock

StreamAcquireQ ==
    /\ pc["stream"] \in {"got_spin", "wait"}
    /\ qspinlock = "free"
    /\ qspinlock' = "stream"
    /\ pc' = [pc EXCEPT !["stream"] = "done"]
    /\ UNCHANGED spinlock

StreamWait ==
    /\ pc["stream"] = "got_spin"
    /\ qspinlock # "free"
    /\ UNCHANGED <<spinlock, qspinlock>>
    /\ pc' = [pc EXCEPT !["stream"] = "wait"]

(* RPC caller steps *)
RPCAcquireQ ==
    /\ pc["rpc"] = "start"
    /\ qspinlock = "free"
    /\ qspinlock' = "rpc"
    /\ pc' = [pc EXCEPT !["rpc"] = "got_q"]
    /\ UNCHANGED spinlock

RPCAcquireSpin ==
    /\ pc["rpc"] \in {"got_q", "wait"}
    /\ spinlock = "free"
    /\ spinlock' = "rpc"
    /\ pc' = [pc EXCEPT !["rpc"] = "done"]
    /\ UNCHANGED qspinlock

RPCWait ==
    /\ pc["rpc"] = "got_q"
    /\ spinlock # "free"
    /\ UNCHANGED <<spinlock, qspinlock>>
    /\ pc' = [pc EXCEPT !["rpc"] = "wait"]

Next ==
    \/ StreamAcquireSpin
    \/ StreamAcquireQ
    \/ StreamWait
    \/ RPCAcquireQ
    \/ RPCAcquireSpin
    \/ RPCWait

Spec == Init /\ [][Next]_<<spinlock, qspinlock, pc>>

Deadlock == <>[] ~(pc["stream"] = "wait" /\ pc["rpc"] = "wait")

====
