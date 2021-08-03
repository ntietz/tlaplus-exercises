---------- MODULE quicksort ----------

EXTENDS TLC, Sequences, Integers
CONSTANTS MinLength, MaxLength, Elements


AllSeqs(minLength, maxLength, elements) == UNION {[1..n -> elements] : n \in minLength..maxLength}

IsSorted(seq) ==
\A idx \in 1..Len(seq)-1:
        seq[idx] <= seq[idx+1]

(*--fair algorithm quicksort

variables
    \* seq = CHOOSE \in AllSeqs(2, 4, 1..10): s = <<2,3,1>>,
    seq \in AllSeqs(6, 7, 1..7),
    length = Len(seq);

define
    SeqIsSorted == <>IsSorted(seq)
    Length == length = Len(seq)
end define

procedure Quicksort(low, high)
variables pivot = 0, i = low, j = low, tmp = 0
begin
    Sort:
        i := low;
        j := low;
        if low >= 1 /\ high >= 1 /\ high <= length /\ low < high then
            pivot := seq[high];

            Sort2:
                while j <= high do
                    if seq[j] <= pivot then
                        Save: tmp := seq[i];
                        Swp1: seq[i] := seq[j];
                        Swp2: seq[j] := tmp;
                        IncI: i := i + 1;
                    end if;

                    IncJ: j := j + 1;
                end while;

            RecurseLeft:
                call Quicksort(low, i - 2);
            RecurseRight:
                call Quicksort(i, high);
        end if;
    Doneso:
        return;
end procedure;

begin
Sorting:
    call Quicksort(1, length);
end algorithm;
*)



\* BEGIN TRANSLATION (chksum(pcal) = "397c9991" /\ chksum(tla) = "e9d8ddcc")
CONSTANT defaultInitValue
VARIABLES seq, length, pc, stack

(* define statement *)
SeqIsSorted == <>IsSorted(seq)
Length == length = Len(seq)

VARIABLES low, high, pivot, i, j, tmp

vars == << seq, length, pc, stack, low, high, pivot, i, j, tmp >>

Init == (* Global variables *)
        /\ seq \in AllSeqs(6, 7, 1..7)
        /\ length = Len(seq)
        (* Procedure Quicksort *)
        /\ low = defaultInitValue
        /\ high = defaultInitValue
        /\ pivot = 0
        /\ i = low
        /\ j = low
        /\ tmp = 0
        /\ stack = << >>
        /\ pc = "Sorting"

Sort == /\ pc = "Sort"
        /\ i' = low
        /\ j' = low
        /\ IF low >= 1 /\ high >= 1 /\ high <= length /\ low < high
              THEN /\ pivot' = seq[high]
                   /\ pc' = "Sort2"
              ELSE /\ pc' = "Doneso"
                   /\ pivot' = pivot
        /\ UNCHANGED << seq, length, stack, low, high, tmp >>

Sort2 == /\ pc = "Sort2"
         /\ IF j <= high
               THEN /\ IF seq[j] <= pivot
                          THEN /\ pc' = "Save"
                          ELSE /\ pc' = "IncJ"
               ELSE /\ pc' = "RecurseLeft"
         /\ UNCHANGED << seq, length, stack, low, high, pivot, i, j, tmp >>

IncJ == /\ pc = "IncJ"
        /\ j' = j + 1
        /\ pc' = "Sort2"
        /\ UNCHANGED << seq, length, stack, low, high, pivot, i, tmp >>

Save == /\ pc = "Save"
        /\ tmp' = seq[i]
        /\ pc' = "Swp1"
        /\ UNCHANGED << seq, length, stack, low, high, pivot, i, j >>

Swp1 == /\ pc = "Swp1"
        /\ seq' = [seq EXCEPT ![i] = seq[j]]
        /\ pc' = "Swp2"
        /\ UNCHANGED << length, stack, low, high, pivot, i, j, tmp >>

Swp2 == /\ pc = "Swp2"
        /\ seq' = [seq EXCEPT ![j] = tmp]
        /\ pc' = "IncI"
        /\ UNCHANGED << length, stack, low, high, pivot, i, j, tmp >>

IncI == /\ pc = "IncI"
        /\ i' = i + 1
        /\ pc' = "IncJ"
        /\ UNCHANGED << seq, length, stack, low, high, pivot, j, tmp >>

RecurseLeft == /\ pc = "RecurseLeft"
               /\ /\ high' = i - 2
                  /\ low' = low
                  /\ stack' = << [ procedure |->  "Quicksort",
                                   pc        |->  "RecurseRight",
                                   pivot     |->  pivot,
                                   i         |->  i,
                                   j         |->  j,
                                   tmp       |->  tmp,
                                   low       |->  low,
                                   high      |->  high ] >>
                               \o stack
               /\ pivot' = 0
               /\ i' = low'
               /\ j' = low'
               /\ tmp' = 0
               /\ pc' = "Sort"
               /\ UNCHANGED << seq, length >>

RecurseRight == /\ pc = "RecurseRight"
                /\ /\ high' = high
                   /\ low' = i
                   /\ stack' = << [ procedure |->  "Quicksort",
                                    pc        |->  "Doneso",
                                    pivot     |->  pivot,
                                    i         |->  i,
                                    j         |->  j,
                                    tmp       |->  tmp,
                                    low       |->  low,
                                    high      |->  high ] >>
                                \o stack
                /\ pivot' = 0
                /\ i' = low'
                /\ j' = low'
                /\ tmp' = 0
                /\ pc' = "Sort"
                /\ UNCHANGED << seq, length >>

Doneso == /\ pc = "Doneso"
          /\ pc' = Head(stack).pc
          /\ pivot' = Head(stack).pivot
          /\ i' = Head(stack).i
          /\ j' = Head(stack).j
          /\ tmp' = Head(stack).tmp
          /\ low' = Head(stack).low
          /\ high' = Head(stack).high
          /\ stack' = Tail(stack)
          /\ UNCHANGED << seq, length >>

Quicksort == Sort \/ Sort2 \/ IncJ \/ Save \/ Swp1 \/ Swp2 \/ IncI
                \/ RecurseLeft \/ RecurseRight \/ Doneso

Sorting == /\ pc = "Sorting"
           /\ /\ high' = length
              /\ low' = 1
              /\ stack' = << [ procedure |->  "Quicksort",
                               pc        |->  "Done",
                               pivot     |->  pivot,
                               i         |->  i,
                               j         |->  j,
                               tmp       |->  tmp,
                               low       |->  low,
                               high      |->  high ] >>
                           \o stack
           /\ pivot' = 0
           /\ i' = low'
           /\ j' = low'
           /\ tmp' = 0
           /\ pc' = "Sort"
           /\ UNCHANGED << seq, length >>

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == Quicksort \/ Sorting
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Next)

Termination == <>(pc = "Done")

\* END TRANSLATION

======================================
