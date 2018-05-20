------------------------------ MODULE Mutex05 ------------------------------
EXTENDS Naturals

(*
Peterson's Algorithm
--algorithm Mutex05
    variable
      turn = 1,
      req_cs   = [p \in 1..2 |-> FALSE];
    
    fair process Proc \in 1..2
    variable
      other = 3 - self;  
    begin
s1:   while TRUE do
ncs:-   skip;
try:    req_cs[self] := TRUE;
s2:     turn := other;
s3:     await (turn = self \/ ~req_cs[other]);
        \* BEGIN CRITICAL SECTION
cs:     skip;
        \* END CRITICAL SECTION
s4:     req_cs[self] := FALSE;
      end while
    end process
end algorithm
*)
\* BEGIN TRANSLATION
VARIABLES turn, req_cs, pc, other

vars == << turn, req_cs, pc, other >>

ProcSet == (1..2)

Init == (* Global variables *)
        /\ turn = 1
        /\ req_cs = [p \in 1..2 |-> FALSE]
        (* Process Proc *)
        /\ other = [self \in 1..2 |-> 3 - self]
        /\ pc = [self \in ProcSet |-> "s1"]

s1(self) == /\ pc[self] = "s1"
            /\ pc' = [pc EXCEPT ![self] = "ncs"]
            /\ UNCHANGED << turn, req_cs, other >>

ncs(self) == /\ pc[self] = "ncs"
             /\ TRUE
             /\ pc' = [pc EXCEPT ![self] = "try"]
             /\ UNCHANGED << turn, req_cs, other >>

try(self) == /\ pc[self] = "try"
             /\ req_cs' = [req_cs EXCEPT ![self] = TRUE]
             /\ pc' = [pc EXCEPT ![self] = "s2"]
             /\ UNCHANGED << turn, other >>

s2(self) == /\ pc[self] = "s2"
            /\ turn' = other[self]
            /\ pc' = [pc EXCEPT ![self] = "s3"]
            /\ UNCHANGED << req_cs, other >>

s3(self) == /\ pc[self] = "s3"
            /\ (turn = self \/ ~req_cs[other[self]])
            /\ pc' = [pc EXCEPT ![self] = "cs"]
            /\ UNCHANGED << turn, req_cs, other >>

cs(self) == /\ pc[self] = "cs"
            /\ TRUE
            /\ pc' = [pc EXCEPT ![self] = "s4"]
            /\ UNCHANGED << turn, req_cs, other >>

s4(self) == /\ pc[self] = "s4"
            /\ req_cs' = [req_cs EXCEPT ![self] = FALSE]
            /\ pc' = [pc EXCEPT ![self] = "s1"]
            /\ UNCHANGED << turn, other >>

Proc(self) == s1(self) \/ ncs(self) \/ try(self) \/ s2(self) \/ s3(self)
                 \/ cs(self) \/ s4(self)

Next == (\E self \in 1..2: Proc(self))

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in 1..2 : WF_vars((pc[self] # "ncs") /\ Proc(self))

\* END TRANSLATION
Try(p) == pc[p] = "try"
InCS(p) == pc[p] = "cs"
Progress == \A p \in ProcSet : Try(p) ~> InCS(p)

=============================================================================
\* Modification History
\* Last modified Sun May 20 22:31:43 BST 2018 by cgdk2
\* Created Fri May 18 09:37:14 BST 2018 by cgdk2
