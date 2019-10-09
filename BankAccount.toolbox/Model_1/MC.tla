---- MODULE MC ----
EXTENDS BankAccount, TLC

\* SPECIFICATION definition @modelBehaviorSpec:0
spec_157062566988611000 ==
Spec
----
\* INVARIANT definition @modelCorrectnessInvariants:0
inv_157062566988612000 ==
(pc[1]="Done"/\pc[2]="Done") => balance=80
----
=============================================================================
\* Modification History
\* Created Wed Oct 09 13:54:29 BST 2019 by cgam1
