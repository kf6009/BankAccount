---------------------------- MODULE BankAccount ----------------------------
EXTENDS Integers

(* Pluscal model follows:
--algorithm BankAccount
  variable balance = 100;
           semaphore = 1;

  process Withdraw \in 1..2    \* 2 processes
    variable current = 0       \* Note how local variables are functions below
    begin
    entry: \* entry protocol 
           await semaphore>0; \* wait for semaphore availability
           semaphore := semaphore - 1; \* update semaphore (hold)
    s1: current := balance;      \* First action, see translation below
    s2: current := current - 10; \* Second section, 
    s3: balance := current;      \* Third section
    exit: \* exit protocol
        semaphore := semaphore + 1; \* release semaphore 
  end process
end algorithm
*)
\* BEGIN TRANSLATION
VARIABLES balance, semaphore, pc, current

vars == << balance, semaphore, pc, current >>

ProcSet == (1..2)

Init == (* Global variables *)
        /\ balance = 100
        /\ semaphore = 1
        (* Process Withdraw *)
        /\ current = [self \in 1..2 |-> 0]
        /\ pc = [self \in ProcSet |-> "entry"]

entry(self) == /\ pc[self] = "entry"
               /\ semaphore>0
               /\ semaphore' = semaphore - 1
               /\ pc' = [pc EXCEPT ![self] = "s1"]
               /\ UNCHANGED << balance, current >>

s1(self) == /\ pc[self] = "s1"
            /\ current' = [current EXCEPT ![self] = balance]
            /\ pc' = [pc EXCEPT ![self] = "s2"]
            /\ UNCHANGED << balance, semaphore >>

s2(self) == /\ pc[self] = "s2"
            /\ current' = [current EXCEPT ![self] = current[self] - 10]
            /\ pc' = [pc EXCEPT ![self] = "s3"]
            /\ UNCHANGED << balance, semaphore >>

s3(self) == /\ pc[self] = "s3"
            /\ balance' = current[self]
            /\ pc' = [pc EXCEPT ![self] = "exit"]
            /\ UNCHANGED << semaphore, current >>

exit(self) == /\ pc[self] = "exit"
              /\ semaphore' = semaphore + 1
              /\ pc' = [pc EXCEPT ![self] = "Done"]
              /\ UNCHANGED << balance, current >>

Withdraw(self) == entry(self) \/ s1(self) \/ s2(self) \/ s3(self)
                     \/ exit(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in 1..2: Withdraw(self))
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION

=============================================================================
\* Modification History
\* Last modified Mon Oct 21 21:09:43 BST 2019 by alun
\* Last modified Wed Oct 09 13:51:02 BST 2019 by cgam1
\* Created Wed Oct 09 13:49:19 BST 2019 by cgam1
