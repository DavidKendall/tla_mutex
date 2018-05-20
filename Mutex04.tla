------------------------------ MODULE Mutex04 ------------------------------
EXTENDS Naturals

(*
--algorithm Mutex04
    variable
      req_cs = [p \in 1..2 |-> FALSE];
    
    fair process Proc \in 1..2
    variable
      other = 3 - self;
    begin
s1:   while TRUE do
ncs:    skip;
try:    req_cs[self] := TRUE;
s2:     while req_cs[other] do
s3:       req_cs[self] := FALSE;
s4:       req_cs[self] := TRUE; 
        end while;
        \* BEGIN CRITICAL SECTION
cs:     skip;
        \* END CRITICAL SECTION
s5:     req_cs[self] := FALSE;
      end while
    end process
end algorithm
*)
\* BEGIN TRANSLATION
VARIABLES req_cs, pc, other

vars == << req_cs, pc, other >>

ProcSet == (1..2)

Init == (* Global variables *)
        /\ req_cs = [p \in 1..2 |-> FALSE]
        (* Process Proc *)
        /\ other = [self \in 1..2 |-> 3 - self]
        /\ pc = [self \in ProcSet |-> "s1"]

s1(self) == /\ pc[self] = "s1"
            /\ pc' = [pc EXCEPT ![self] = "ncs"]
            /\ UNCHANGED << req_cs, other >>

ncs(self) == /\ pc[self] = "ncs"
             /\ TRUE
             /\ pc' = [pc EXCEPT ![self] = "try"]
             /\ UNCHANGED << req_cs, other >>

try(self) == /\ pc[self] = "try"
             /\ req_cs' = [req_cs EXCEPT ![self] = TRUE]
             /\ pc' = [pc EXCEPT ![self] = "s2"]
             /\ other' = other

s2(self) == /\ pc[self] = "s2"
            /\ IF req_cs[other[self]]
                  THEN /\ pc' = [pc EXCEPT ![self] = "s3"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "cs"]
            /\ UNCHANGED << req_cs, other >>

s3(self) == /\ pc[self] = "s3"
            /\ req_cs' = [req_cs EXCEPT ![self] = FALSE]
            /\ pc' = [pc EXCEPT ![self] = "s4"]
            /\ other' = other

s4(self) == /\ pc[self] = "s4"
            /\ req_cs' = [req_cs EXCEPT ![self] = TRUE]
            /\ pc' = [pc EXCEPT ![self] = "s2"]
            /\ other' = other

cs(self) == /\ pc[self] = "cs"
            /\ TRUE
            /\ pc' = [pc EXCEPT ![self] = "s5"]
            /\ UNCHANGED << req_cs, other >>

s5(self) == /\ pc[self] = "s5"
            /\ req_cs' = [req_cs EXCEPT ![self] = FALSE]
            /\ pc' = [pc EXCEPT ![self] = "s1"]
            /\ other' = other

Proc(self) == s1(self) \/ ncs(self) \/ try(self) \/ s2(self) \/ s3(self)
                 \/ s4(self) \/ cs(self) \/ s5(self)

Next == (\E self \in 1..2: Proc(self))

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in 1..2 : WF_vars(Proc(self))

\* END TRANSLATION
Try(p) == pc[p] = "try"
InCS(p) == pc[p] = "cs"
Mutex == ~(InCS(1) /\ InCS(2))
Progress == \A p \in ProcSet : Try(p) ~> InCS(p)
=============================================================================
\* Modification History
\* Last modified Sun May 20 22:30:06 BST 2018 by cgdk2
\* Created Sun May 20 18:25:08 BST 2018 by cgdk2
