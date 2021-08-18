---------- MODULE gcounter ----------

EXTENDS TLC, Integers

NodeCount == 3
Nodes == 1..NodeCount
StepLimit == 10

InitializedCounter == [n \in Nodes |-> 0]

Max(x, y) == IF x > y THEN x ELSE y
MaxCounter(xs, ys) == [n \in Nodes |-> Max(xs[n], ys[n])]

(* --algorithm gcounter

variables
    state = [n \in Nodes |-> InitializedCounter],
    steps = 0;

macro increment(n)
begin
    state[n][n] := state[n][n] + 1;
end macro;

macro merge(n, m)
begin
    state[n] := MaxCounter(state[n], state[m]);
end macro;

fair process node \in 1..NodeCount
variables
    next = 1;
begin
Node:
    while steps < StepLimit do
        either
        Increment:
            increment(self);
            steps := steps + 1;
        or
        Merge:
            with other \in Nodes \ {self} do
                merge(self, other);
            end with;
        end either;

    end while;
Converge:
    while TRUE do
        merge(self, next);
        next := IF next >= NodeCount THEN 1 ELSE next + 1;
    end while;
end process;

end algorithm;
*)
\* BEGIN TRANSLATION (chksum(pcal) = "8460205f" /\ chksum(tla) = "749a48fd")
VARIABLES state, steps, pc, next

vars == << state, steps, pc, next >>

ProcSet == (1..NodeCount)

Init == (* Global variables *)
        /\ state = [n \in Nodes |-> InitializedCounter]
        /\ steps = 0
        (* Process node *)
        /\ next = [self \in 1..NodeCount |-> 1]
        /\ pc = [self \in ProcSet |-> "Node"]

Node(self) == /\ pc[self] = "Node"
              /\ IF steps < StepLimit
                    THEN /\ \/ /\ pc' = [pc EXCEPT ![self] = "Increment"]
                            \/ /\ pc' = [pc EXCEPT ![self] = "Merge"]
                    ELSE /\ pc' = [pc EXCEPT ![self] = "Converge"]
              /\ UNCHANGED << state, steps, next >>

Increment(self) == /\ pc[self] = "Increment"
                   /\ state' = [state EXCEPT ![self][self] = state[self][self] + 1]
                   /\ steps' = steps + 1
                   /\ pc' = [pc EXCEPT ![self] = "Node"]
                   /\ next' = next

Merge(self) == /\ pc[self] = "Merge"
               /\ \E other \in Nodes \ {self}:
                    state' = [state EXCEPT ![self] = MaxCounter(state[self], state[other])]
               /\ pc' = [pc EXCEPT ![self] = "Node"]
               /\ UNCHANGED << steps, next >>

Converge(self) == /\ pc[self] = "Converge"
                  /\ state' = [state EXCEPT ![self] = MaxCounter(state[self], state[next[self]])]
                  /\ next' = [next EXCEPT ![self] = IF next[self] >= NodeCount THEN 1 ELSE next[self] + 1]
                  /\ pc' = [pc EXCEPT ![self] = "Converge"]
                  /\ steps' = steps

node(self) == Node(self) \/ Increment(self) \/ Merge(self)
                 \/ Converge(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in 1..NodeCount: node(self))
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in 1..NodeCount : WF_vars(node(self))

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION

EventuallyConsistent == steps < StepLimit \/ <>[](\A n \in Nodes, m \in Nodes: state[n] = state[m])

=====================================
