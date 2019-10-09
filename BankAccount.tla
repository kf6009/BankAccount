---------------------------- MODULE BankAccount ----------------------------
EXTENDS Integers

(* Pluscal model follows:
--algorithm BankAccount
  variable balance = 100

  process Withdraw \in 1..2
    variable current = 0
    begin
    s1: current := balance;
    s2: current := current - 10;
    s3: balance := current
  end process
end algorithm
*)
\* BEGIN TRANSLATION
VARIABLES balance, pc, current

vars == << balance, pc, current >>

ProcSet == (1..2)

Init == (* Global variables *)
        /\ balance = 100
        (* Process Withdraw *)
        /\ current = [self \in 1..2 |-> 0]
        /\ pc = [self \in ProcSet |-> "s1"]

s1(self) == /\ pc[self] = "s1"
            /\ current' = [current EXCEPT ![self] = balance]
            /\ pc' = [pc EXCEPT ![self] = "s2"]
            /\ UNCHANGED balance

s2(self) == /\ pc[self] = "s2"
            /\ current' = [current EXCEPT ![self] = current[self] - 10]
            /\ pc' = [pc EXCEPT ![self] = "s3"]
            /\ UNCHANGED balance

s3(self) == /\ pc[self] = "s3"
            /\ balance' = current[self]
            /\ pc' = [pc EXCEPT ![self] = "Done"]
            /\ UNCHANGED current

Withdraw(self) == s1(self) \/ s2(self) \/ s3(self)

Next == (\E self \in 1..2: Withdraw(self))
           \/ (* Disjunct to prevent deadlock on termination *)
              ((\A self \in ProcSet: pc[self] = "Done") /\ UNCHANGED vars)

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION


=============================================================================
\* Modification History
\* Last modified Wed Oct 09 13:51:02 BST 2019 by cgam1
\* Created Wed Oct 09 13:49:19 BST 2019 by cgam1
