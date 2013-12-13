(* Proof machinery specific to SK.v *)
Require Export Util.

Ltac sk_tac := unfold complement, equiv; program_simpl; deqs.

