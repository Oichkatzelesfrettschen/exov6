----------------------- MODULE VectorTimestamps ------------------------
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANT NumDomains \* The number of entities tracked in the vector timestamp

ASSUME NumDomains >= 1

\* Type check for a single vector timestamp structure
IsVectorTimestamp(vt) ==
    /\ DOMAIN vt = 0..(NumDomains-1)
    /\ ({ i \in DOMAIN vt : vt[i] \in Nat } = DOMAIN vt)

\* Operator: Initializes a vector timestamp for NumDomains
VTInit == [ i \in 0..(NumDomains-1) |-> 0 ]

\* Operator: Increments the local component of a vector timestamp
\* vt: the vector timestamp
\* idx: the index of the local component (0 to NumDomains-1)
VTLocalEvent(vt, idx) ==
    \* Precondition: Assert(idx \in 0..(NumDomains-1) /\ IsVectorTimestamp(vt), "VTLocalEvent: invalid parameters")
    [vt EXCEPT ![idx] = @[idx] + 1]

\* Operator: Merges two vector timestamps (component-wise maximum)
\* Used by a receiver. vt1 is local, vt2 is received
VTMerge(vt1, vt2) ==
    \* Precondition: Assert(IsVectorTimestamp(vt1) /\ IsVectorTimestamp(vt2), "VTMerge: invalid parameters")
    [ i \in 0..(NumDomains-1) |-> IF vt1[i] > vt2[i] THEN vt1[i] ELSE vt2[i] ]

\* Operator: Strictly less than for vector timestamps (happened-before)
\* vt1 < vt2
VTLt(vt1, vt2) ==
    /\ Assert(IsVectorTimestamp(vt1) /\ IsVectorTimestamp(vt2),
              "VTLt: invalid parameters")
    /\ ({ i \in 0..(NumDomains-1) : vt1[i] <= vt2[i] } = 0..(NumDomains-1))
    /\ ({ j \in 0..(NumDomains-1) : vt1[j] < vt2[j] } /= {})

\* Operator: Less than or equal for vector timestamps
\* vt1 <= vt2
VTLeq(vt1, vt2) ==
    /\ Assert(IsVectorTimestamp(vt1) /\ IsVectorTimestamp(vt2),
           "VTLeq: invalid parameters")
    /\ ({ i \in 0..(NumDomains-1) : vt1[i] <= vt2[i] } = 0..(NumDomains-1))

\* Operator: Concurrency check for vector timestamps
\* vt1 || vt2
VTConcurrent(vt1, vt2) ==
    /\ Assert(IsVectorTimestamp(vt1) /\ IsVectorTimestamp(vt2),
              "VTConcurrent: invalid parameters")
    /\ ~VTLt(vt1, vt2)
    /\ ~VTLt(vt2, vt1)

=============================================================================
