---------------------------- MODULE BankAccount ----------------------------
EXTENDS Integers

(* Pluscal model follows:
--algorithm BankAccount
  variable balance = 100;    \* Global, with initial value
           mutex = "free";   \* Mutex initially available

  process Withdraw \in 1..2
    variable current = 0;    (* Local variable: note how this translate into a 
                                function mapping process id to the value
                             *)
    begin
    entry: \* entry protocol
        await mutex = "free" ; \* obtain mutex
        mutex := "held" ;      \* lock mutex
    s1: current := balance;      \* Step one, note how it translates to an action
    s2: current := current - 10; \* Second step, has to be another step to update current
    s3: balance := current;      \* Third step 
    exit: \* exit protocol
        mutex := "free"   \* release mutex
  end process
end algorithm
*)
\* BEGIN TRANSLATION
VARIABLES balance, mutex, pc, current

vars == << balance, mutex, pc, current >>

ProcSet == (1..2)

Init == (* Global variables *)
        /\ balance = 100
        /\ mutex = "free"
        (* Process Withdraw *)
        /\ current = [self \in 1..2 |-> 0]
        /\ pc = [self \in ProcSet |-> "entry"]

entry(self) == /\ pc[self] = "entry"
               /\ mutex = "free"
               /\ mutex' = "held"
               /\ pc' = [pc EXCEPT ![self] = "s1"]
               /\ UNCHANGED << balance, current >>

s1(self) == /\ pc[self] = "s1"
            /\ current' = [current EXCEPT ![self] = balance]
            /\ pc' = [pc EXCEPT ![self] = "s2"]
            /\ UNCHANGED << balance, mutex >>

s2(self) == /\ pc[self] = "s2"
            /\ current' = [current EXCEPT ![self] = current[self] - 10]
            /\ pc' = [pc EXCEPT ![self] = "s3"]
            /\ UNCHANGED << balance, mutex >>

s3(self) == /\ pc[self] = "s3"
            /\ balance' = current[self]
            /\ pc' = [pc EXCEPT ![self] = "exit"]
            /\ UNCHANGED << mutex, current >>

exit(self) == /\ pc[self] = "exit"
              /\ mutex' = "free"
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

MutexInvariant == mutex \in {"free", "held"}
=============================================================================
\* Modification History
\* Last modified Mon Oct 21 21:17:20 BST 2019 by alun
\* Last modified Wed Oct 09 13:51:02 BST 2019 by cgam1
\* Created Wed Oct 09 13:49:19 BST 2019 by cgam1
