------------------------------ MODULE Mutex03 ------------------------------
EXTENDS Naturals

(*
--algorithm Mutex03
    variable
      turn = 1;
     
    fair process Proc \in 1..2
    variable
      other = 3 - self; 
    begin
s1:   while TRUE do
ncs:-   skip;
try:    await turn = self;
        \* BEGIN CRITICAL SECTION
cs:     skip;
        \* END CRITICAL SECTION
s2:     turn := other;
      end while
    end process
end algorithm
*)
\* BEGIN TRANSLATION
VARIABLES turn, pc, other

vars == << turn, pc, other >>

ProcSet == (1..2)

Init == (* Global variables *)
        /\ turn = 1
        (* Process Proc *)
        /\ other = [self \in 1..2 |-> 3 - self]
        /\ pc = [self \in ProcSet |-> "s1"]

s1(self) == /\ pc[self] = "s1"
            /\ pc' = [pc EXCEPT ![self] = "ncs"]
            /\ UNCHANGED << turn, other >>

ncs(self) == /\ pc[self] = "ncs"
             /\ TRUE
             /\ pc' = [pc EXCEPT ![self] = "try"]
             /\ UNCHANGED << turn, other >>

try(self) == /\ pc[self] = "try"
             /\ turn = self
             /\ pc' = [pc EXCEPT ![self] = "cs"]
             /\ UNCHANGED << turn, other >>

cs(self) == /\ pc[self] = "cs"
            /\ TRUE
            /\ pc' = [pc EXCEPT ![self] = "s2"]
            /\ UNCHANGED << turn, other >>

s2(self) == /\ pc[self] = "s2"
            /\ turn' = other[self]
            /\ pc' = [pc EXCEPT ![self] = "s1"]
            /\ other' = other

Proc(self) == s1(self) \/ ncs(self) \/ try(self) \/ cs(self) \/ s2(self)

Next == (\E self \in 1..2: Proc(self))

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in 1..2 : WF_vars((pc[self] # "ncs") /\ Proc(self))

\* END TRANSLATION
Try(p) == pc[p] = "try"
InCS(p) == pc[p] = "cs"
Persistent(p) == []<> Try(p)
LSpec == Spec /\ Persistent(1) /\ Persistent(2)
Mutex == ~(InCS(1) /\ InCS(2))
Progress == \A p \in ProcSet : Try(p) ~> InCS(p)

=============================================================================
\* Modification History
\* Last modified Sun May 20 22:08:33 BST 2018 by cgdk2
\* Created Wed May 16 19:07:50 BST 2018 by cgdk2
