---------- MODULE deadlock ----------
EXTENDS TLC, Integers, Sequences

NumPhilosophers == 4
Philosophers == 1..NumPhilosophers

LeftFork(p) == p
RightFork(p) == IF p = NumPhilosophers THEN 1 ELSE p + 1


(* --algorithm dining
variables
    \* the boolean status indicates available or not
    \* TODO: convert these to just straight up sets!
    tableForks = [id \in Philosophers |-> TRUE],
    heldForks = [id \in Philosophers |-> [x \in Philosophers |-> FALSE]];

procedure pick_up_fork(p, f)
begin
WaitForIt:
    await tableForks[f] = TRUE;
    tableForks[f] := FALSE;
    heldForks[p][f] := TRUE;
    return;
end procedure;

procedure drop_fork(p, f)
begin
CheckYoSelf:
    assert heldForks[p][f] = TRUE;
    tableForks[f] := TRUE;
    heldForks[p][f] := FALSE;
    return;
end procedure;


\* we don't let the philosophers spontaneously leave the table or fall asleep on their plate.
\* they said they'll dine, now dine, dammit!
fair process philosopher \in Philosophers
variables
    hasEaten = FALSE;

begin
Dining:
    assert RightFork(1) = 2;
    assert RightFork(4) = 1;
    EatLoop: while TRUE do
        UpLeft: call pick_up_fork(self, LeftFork(self));
        UpRight: call pick_up_fork(self, RightFork(self));
        DownRight: call drop_fork(self, RightFork(self));
        DownLeft: call drop_fork(self, LeftFork(self));

    end while;
end process;

end algorithm;

*)


\* BEGIN TRANSLATION (chksum(pcal) = "a512f736" /\ chksum(tla) = "3417b653")
\* Parameter p of procedure pick_up_fork at line 18 col 24 changed to p_
\* Parameter f of procedure pick_up_fork at line 18 col 27 changed to f_
CONSTANT defaultInitValue
VARIABLES tableForks, heldForks, pc, stack, p_, f_, p, f, hasEaten

vars == << tableForks, heldForks, pc, stack, p_, f_, p, f, hasEaten >>

ProcSet == (Philosophers)

Init == (* Global variables *)
        /\ tableForks = [id \in Philosophers |-> TRUE]
        /\ heldForks = [id \in Philosophers |-> [x \in Philosophers |-> FALSE]]
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
                   /\ tableForks[f_[self]] = TRUE
                   /\ tableForks' = [tableForks EXCEPT ![f_[self]] = FALSE]
                   /\ heldForks' = [heldForks EXCEPT ![p_[self]][f_[self]] = TRUE]
                   /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                   /\ p_' = [p_ EXCEPT ![self] = Head(stack[self]).p_]
                   /\ f_' = [f_ EXCEPT ![self] = Head(stack[self]).f_]
                   /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                   /\ UNCHANGED << p, f, hasEaten >>

pick_up_fork(self) == WaitForIt(self)

CheckYoSelf(self) == /\ pc[self] = "CheckYoSelf"
                     /\ Assert(heldForks[p[self]][f[self]] = TRUE,
                               "Failure of assertion at line 30, column 5.")
                     /\ tableForks' = [tableForks EXCEPT ![f[self]] = TRUE]
                     /\ heldForks' = [heldForks EXCEPT ![p[self]][f[self]] = FALSE]
                     /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                     /\ p' = [p EXCEPT ![self] = Head(stack[self]).p]
                     /\ f' = [f EXCEPT ![self] = Head(stack[self]).f]
                     /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                     /\ UNCHANGED << p_, f_, hasEaten >>

drop_fork(self) == CheckYoSelf(self)

Dining(self) == /\ pc[self] = "Dining"
                /\ Assert(RightFork(1) = 2,
                          "Failure of assertion at line 45, column 5.")
                /\ Assert(RightFork(4) = 1,
                          "Failure of assertion at line 46, column 5.")
                /\ pc' = [pc EXCEPT ![self] = "EatLoop"]
                /\ UNCHANGED << tableForks, heldForks, stack, p_, f_, p, f,
                                hasEaten >>

EatLoop(self) == /\ pc[self] = "EatLoop"
                 /\ pc' = [pc EXCEPT ![self] = "UpLeft"]
                 /\ UNCHANGED << tableForks, heldForks, stack, p_, f_, p, f,
                                 hasEaten >>

UpLeft(self) == /\ pc[self] = "UpLeft"
                /\ /\ f_' = [f_ EXCEPT ![self] = LeftFork(self)]
                   /\ p_' = [p_ EXCEPT ![self] = self]
                   /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "pick_up_fork",
                                                            pc        |->  "UpRight",
                                                            p_        |->  p_[self],
                                                            f_        |->  f_[self] ] >>
                                                        \o stack[self]]
                /\ pc' = [pc EXCEPT ![self] = "WaitForIt"]
                /\ UNCHANGED << tableForks, heldForks, p, f, hasEaten >>

UpRight(self) == /\ pc[self] = "UpRight"
                 /\ /\ f_' = [f_ EXCEPT ![self] = RightFork(self)]
                    /\ p_' = [p_ EXCEPT ![self] = self]
                    /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "pick_up_fork",
                                                             pc        |->  "DownRight",
                                                             p_        |->  p_[self],
                                                             f_        |->  f_[self] ] >>
                                                         \o stack[self]]
                 /\ pc' = [pc EXCEPT ![self] = "WaitForIt"]
                 /\ UNCHANGED << tableForks, heldForks, p, f, hasEaten >>

DownRight(self) == /\ pc[self] = "DownRight"
                   /\ /\ f' = [f EXCEPT ![self] = RightFork(self)]
                      /\ p' = [p EXCEPT ![self] = self]
                      /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "drop_fork",
                                                               pc        |->  "DownLeft",
                                                               p         |->  p[self],
                                                               f         |->  f[self] ] >>
                                                           \o stack[self]]
                   /\ pc' = [pc EXCEPT ![self] = "CheckYoSelf"]
                   /\ UNCHANGED << tableForks, heldForks, p_, f_, hasEaten >>

DownLeft(self) == /\ pc[self] = "DownLeft"
                  /\ /\ f' = [f EXCEPT ![self] = LeftFork(self)]
                     /\ p' = [p EXCEPT ![self] = self]
                     /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "drop_fork",
                                                              pc        |->  "EatLoop",
                                                              p         |->  p[self],
                                                              f         |->  f[self] ] >>
                                                          \o stack[self]]
                  /\ pc' = [pc EXCEPT ![self] = "CheckYoSelf"]
                  /\ UNCHANGED << tableForks, heldForks, p_, f_, hasEaten >>

philosopher(self) == Dining(self) \/ EatLoop(self) \/ UpLeft(self)
                        \/ UpRight(self) \/ DownRight(self)
                        \/ DownLeft(self)

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
