---------- MODULE livelock ----------
EXTENDS TLC, Integers, Sequences

NumPhilosophers == 4
Philosophers == 1..NumPhilosophers

LeftFork(p) == p
RightFork(p) == IF p = NumPhilosophers THEN 1 ELSE p + 1
AdjacentForks(p)  == {LeftFork(p), RightFork(p)}


(* --algorithm dining
variables
    \* the boolean status indicates available or not
    \* TODO: convert these to just straight up sets!
    tableForks = {x \in Philosophers: TRUE},
    heldForks = [id \in Philosophers |-> {}];

define
    NeededForks(p) == AdjacentForks(p) \ heldForks[p]
    AvailableForks(p) == AdjacentForks(p) \intersect tableForks
    NextFork(p) == CHOOSE f \in NeededForks(p):
                    /\ \A g \in NeededForks(p): f <= g
end define;

procedure pick_up_fork(p, f)
begin
WaitForIt:
    await f \in tableForks;
    tableForks := tableForks \ {f};
    heldForks[p] := heldForks[p] \union {f};
    return;
end procedure;

procedure drop_fork(p, f)
begin
CheckYoSelf:
    assert f \in heldForks[p];
    tableForks := tableForks \union {f};
    heldForks[p] := heldForks[p] \ {f};
    return;
end procedure;


\* we don't let the philosophers spontaneously leave the table or fall asleep on their plate.
\* they said they'll dine, now dine, dammit!
fair process philosopher \in Philosophers
variables
    hasEaten = FALSE;

begin
Dining:
    while ~hasEaten do
        PickUp:
        while AvailableForks(self) /= {} do
            with upF \in NeededForks(self) do
                call pick_up_fork(self, upF);
            end with;
        end while;

        if NeededForks(self) = {} then
            hasEaten := TRUE;
        end if;

        PutDown:
        while heldForks[self] /= {} do
            with downF \in heldForks[self] do
                call drop_fork(self, downF);
            end with;
        end while;
    end while;
end process;

end algorithm;

*)


\* BEGIN TRANSLATION (chksum(pcal) = "fbf60ae9" /\ chksum(tla) = "d0d4bc2a")
\* Parameter p of procedure pick_up_fork at line 26 col 24 changed to p_
\* Parameter f of procedure pick_up_fork at line 26 col 27 changed to f_
CONSTANT defaultInitValue
VARIABLES tableForks, heldForks, pc, stack

(* define statement *)
NeededForks(p) == AdjacentForks(p) \ heldForks[p]
AvailableForks(p) == AdjacentForks(p) \intersect tableForks
NextFork(p) == CHOOSE f \in NeededForks(p):
                /\ \A g \in NeededForks(p): f <= g

VARIABLES p_, f_, p, f, hasEaten

vars == << tableForks, heldForks, pc, stack, p_, f_, p, f, hasEaten >>

ProcSet == (Philosophers)

Init == (* Global variables *)
        /\ tableForks = {x \in Philosophers: TRUE}
        /\ heldForks = [id \in Philosophers |-> {}]
        (* Procedure pick_up_fork *)
        /\ p_ = [ self \in ProcSet |-> defaultInitValue]
        /\ f_ = [ self \in ProcSet |-> defaultInitValue]
        (* Procedure drop_fork *)
        /\ p = [ self \in ProcSet |-> defaultInitValue]
        /\ f = [ self \in ProcSet |-> defaultInitValue]
        (* Process philosopher *)
        /\ hasEaten = [self \in Philosophers |-> FALSE]
        /\ stack = [self \in ProcSet |-> << >>]
        /\ pc = [self \in ProcSet |-> "Dining"]

WaitForIt(self) == /\ pc[self] = "WaitForIt"
                   /\ f_[self] \in tableForks
                   /\ tableForks' = tableForks \ {f_[self]}
                   /\ heldForks' = [heldForks EXCEPT ![p_[self]] = heldForks[p_[self]] \union {f_[self]}]
                   /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                   /\ p_' = [p_ EXCEPT ![self] = Head(stack[self]).p_]
                   /\ f_' = [f_ EXCEPT ![self] = Head(stack[self]).f_]
                   /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                   /\ UNCHANGED << p, f, hasEaten >>

pick_up_fork(self) == WaitForIt(self)

CheckYoSelf(self) == /\ pc[self] = "CheckYoSelf"
                     /\ Assert(f[self] \in heldForks[p[self]],
                               "Failure of assertion at line 38, column 5.")
                     /\ tableForks' = (tableForks \union {f[self]})
                     /\ heldForks' = [heldForks EXCEPT ![p[self]] = heldForks[p[self]] \ {f[self]}]
                     /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                     /\ p' = [p EXCEPT ![self] = Head(stack[self]).p]
                     /\ f' = [f EXCEPT ![self] = Head(stack[self]).f]
                     /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                     /\ UNCHANGED << p_, f_, hasEaten >>

drop_fork(self) == CheckYoSelf(self)

Dining(self) == /\ pc[self] = "Dining"
                /\ IF ~hasEaten[self]
                      THEN /\ pc' = [pc EXCEPT ![self] = "PickUp"]
                      ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                /\ UNCHANGED << tableForks, heldForks, stack, p_, f_, p, f,
                                hasEaten >>

PickUp(self) == /\ pc[self] = "PickUp"
                /\ IF AvailableForks(self) /= {}
                      THEN /\ \E upF \in NeededForks(self):
                                /\ /\ f_' = [f_ EXCEPT ![self] = upF]
                                   /\ p_' = [p_ EXCEPT ![self] = self]
                                   /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "pick_up_fork",
                                                                            pc        |->  "PickUp",
                                                                            p_        |->  p_[self],
                                                                            f_        |->  f_[self] ] >>
                                                                        \o stack[self]]
                                /\ pc' = [pc EXCEPT ![self] = "WaitForIt"]
                           /\ UNCHANGED hasEaten
                      ELSE /\ IF NeededForks(self) = {}
                                 THEN /\ hasEaten' = [hasEaten EXCEPT ![self] = TRUE]
                                 ELSE /\ TRUE
                                      /\ UNCHANGED hasEaten
                           /\ pc' = [pc EXCEPT ![self] = "PutDown"]
                           /\ UNCHANGED << stack, p_, f_ >>
                /\ UNCHANGED << tableForks, heldForks, p, f >>

PutDown(self) == /\ pc[self] = "PutDown"
                 /\ IF heldForks[self] /= {}
                       THEN /\ \E downF \in heldForks[self]:
                                 /\ /\ f' = [f EXCEPT ![self] = downF]
                                    /\ p' = [p EXCEPT ![self] = self]
                                    /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "drop_fork",
                                                                             pc        |->  "PutDown",
                                                                             p         |->  p[self],
                                                                             f         |->  f[self] ] >>
                                                                         \o stack[self]]
                                 /\ pc' = [pc EXCEPT ![self] = "CheckYoSelf"]
                       ELSE /\ pc' = [pc EXCEPT ![self] = "Dining"]
                            /\ UNCHANGED << stack, p, f >>
                 /\ UNCHANGED << tableForks, heldForks, p_, f_, hasEaten >>

philosopher(self) == Dining(self) \/ PickUp(self) \/ PutDown(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in ProcSet: pick_up_fork(self) \/ drop_fork(self))
           \/ (\E self \in Philosophers: philosopher(self))
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in Philosophers : /\ WF_vars(philosopher(self))
                                      /\ WF_vars(pick_up_fork(self))
                                      /\ WF_vars(drop_fork(self))

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION

EveryoneEats == <>(\A p_1 \in Philosophers: hasEaten[p_1])

==============================================
