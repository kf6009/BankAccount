---- MODULE MC ----
EXTENDS BankAccount, TLC

\* INVARIANT definition @modelCorrectnessInvariants:0
inv_157166522557359000 ==
(pc[1]="Done"/\pc[2]="Done") => balance=80
----
=============================================================================
\* Modification History
\* Created Mon Oct 21 14:40:25 BST 2019 by alun
