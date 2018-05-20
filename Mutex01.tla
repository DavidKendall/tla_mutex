------------------------------ MODULE Mutex01 ------------------------------
EXTENDS Naturals

(*
--algorithm Mutex01
    variable
      entry = "allowed";
    process Proc \in 1..2
    begin
s1:   while TRUE do
s2:     await entry = "allowed";
s3:     entry := "forbidden";
        \* BEGIN CRITICAL SECTION
cs:     skip;
        \* END CRITICAL SECTION
s4:     entry := "allowed"
      end while
    end process
end algorithm
*)
\* BEGIN TRANSLATION
VARIABLES entry, pc

vars == << entry, pc >>

ProcSet == (1..2)

Init == (* Global variables *)
        /\ entry = "allowed"
        /\ pc = [self \in ProcSet |-> "s1"]

s1(self) == /\ pc[self] = "s1"
            /\ pc' = [pc EXCEPT ![self] = "s2"]
            /\ entry' = entry

s2(self) == /\ pc[self] = "s2"
            /\ entry = "allowed"
            /\ pc' = [pc EXCEPT ![self] = "s3"]
            /\ entry' = entry

s3(self) == /\ pc[self] = "s3"
            /\ entry' = "forbidden"
            /\ pc' = [pc EXCEPT ![self] = "cs"]

cs(self) == /\ pc[self] = "cs"
            /\ TRUE
            /\ pc' = [pc EXCEPT ![self] = "s4"]
            /\ entry' = entry

s4(self) == /\ pc[self] = "s4"
            /\ entry' = "allowed"
            /\ pc' = [pc EXCEPT ![self] = "s1"]

Proc(self) == s1(self) \/ s2(self) \/ s3(self) \/ cs(self) \/ s4(self)

Next == (\E self \in 1..2: Proc(self))

Spec == Init /\ [][Next]_vars

\* END TRANSLATION

TypeInvariant == /\ entry \in {"allowed", "forbidden"}
                 /\ pc \in [ProcSet -> {"s1", "s2", "s3", "cs", "s4"}]
InCS(p) == pc[p] = "cs"
Mutex == ~(InCS(1) /\ InCS(2))
=============================================================================
\* Modification History
\* Last modified Sun May 20 22:23:28 BST 2018 by cgdk2
\* Created Sun May 13 19:43:36 BST 2018 by cgdk2
