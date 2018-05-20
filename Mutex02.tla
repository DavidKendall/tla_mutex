------------------------------ MODULE Mutex02 ------------------------------
EXTENDS Naturals
(*
--algorithm Mutex02
    variable 
      req_cs = [i \in 1..2 |-> FALSE];
  
    process Proc \in 1..2
      variable other = 3 - self;
    begin
s1:   while TRUE do
s2:     req_cs[self] := TRUE;
s3:     await ~req_cs[other];
        \* BEGIN CRITICAL SECTION
cs:     skip;
        \* END CRITICAL SECTION
s4:     req_cs[self] := FALSE;
      end while
    end process
end algorithm
*)
\* BEGIN TRANSLATION
VARIABLES req_cs, pc, other

vars == << req_cs, pc, other >>

ProcSet == (1..2)

Init == (* Global variables *)
        /\ req_cs = [i \in 1..2 |-> FALSE]
        (* Process Proc *)
        /\ other = [self \in 1..2 |-> 3 - self]
        /\ pc = [self \in ProcSet |-> "s1"]

s1(self) == /\ pc[self] = "s1"
            /\ pc' = [pc EXCEPT ![self] = "s2"]
            /\ UNCHANGED << req_cs, other >>

s2(self) == /\ pc[self] = "s2"
            /\ req_cs' = [req_cs EXCEPT ![self] = TRUE]
            /\ pc' = [pc EXCEPT ![self] = "s3"]
            /\ other' = other

s3(self) == /\ pc[self] = "s3"
            /\ ~req_cs[other[self]]
            /\ pc' = [pc EXCEPT ![self] = "cs"]
            /\ UNCHANGED << req_cs, other >>

cs(self) == /\ pc[self] = "cs"
            /\ TRUE
            /\ pc' = [pc EXCEPT ![self] = "s4"]
            /\ UNCHANGED << req_cs, other >>

s4(self) == /\ pc[self] = "s4"
            /\ req_cs' = [req_cs EXCEPT ![self] = FALSE]
            /\ pc' = [pc EXCEPT ![self] = "s1"]
            /\ other' = other

Proc(self) == s1(self) \/ s2(self) \/ s3(self) \/ cs(self) \/ s4(self)

Next == (\E self \in 1..2: Proc(self))

Spec == Init /\ [][Next]_vars

\* END TRANSLATION
InCS(p) == pc[p] = "cs"
Mutex == ~(InCS(1) /\ InCS(2))

=============================================================================
\* Modification History
\* Last modified Sun May 20 19:34:16 BST 2018 by cgdk2
\* Created Mon May 14 00:20:35 BST 2018 by cgdk2
