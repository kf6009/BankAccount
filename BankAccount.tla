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

=============================================================================
\* Modification History
\* Last modified Mon Oct 21 21:10:29 BST 2019 by alun
\* Last modified Wed Oct 09 13:51:02 BST 2019 by cgam1
\* Created Wed Oct 09 13:49:19 BST 2019 by cgam1
