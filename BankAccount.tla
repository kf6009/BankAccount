---------------------------- MODULE BankAccount ----------------------------
EXTENDS Integers

(* Pluscal model follows:
--algorithm BankAccount
  variable balance = 100;

  process Withdraw \in 1..2    \* 2 processes
    variable current = 0       \* Note how local variables are functions below
    begin
    s1: current := balance;      \* First action, see translation below
    s2: current := current - 10; \* Second section, 
    s3: balance := current;      \* Third section
  end process
end algorithm
*)

=============================================================================
\* Modification History
\* Last modified Mon Oct 21 20:57:10 BST 2019 by alun
\* Last modified Wed Oct 09 13:51:02 BST 2019 by cgam1
\* Created Wed Oct 09 13:49:19 BST 2019 by cgam1
