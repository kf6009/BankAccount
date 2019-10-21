---- MODULE MC ----
EXTENDS BankAccount, TLC

\* INVARIANT definition @modelCorrectnessInvariants:0
inv_15716885985912000 ==
(pc[1]="Done"/\pc[2]="Done") => balance=80
----
=============================================================================
\* Modification History
\* Created Mon Oct 21 21:09:58 BST 2019 by alun
