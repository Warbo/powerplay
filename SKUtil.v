(* Proof machinery specific to SK.v *)
Require Export Util.

(* Solves lots of obligations quite well *)
Ltac sk_tac := unfold complement, equiv; program_simpl; deqs.
