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

MutexInvariant == mutex \in {"free", "held"}
=============================================================================
\* Modification History
\* Last modified Mon Oct 21 21:18:00 BST 2019 by alun
\* Last modified Wed Oct 09 13:51:02 BST 2019 by cgam1
\* Created Wed Oct 09 13:49:19 BST 2019 by cgam1
