(* A very useful library *)
Require Export Program.

(* Useful for proving things aren't equal *)
Ltac neq :=
  apply right; intro; dependent destruction H;
  match goal with
        [ c : ?e -> False |- False ] => try (apply (c eq_refl))
  end.

(* Provide finite sets, with the name "fin" rather than "t" *)
Require Export Fin.
Definition fin := Fin.t.

(* Decidable equality of elements of the same finite set *)
Require Export EquivDec.
Fixpoint fin_eq {n} (x y : fin n) : {x === y} + {x =/= y}.
  (* Case x = F1 *)
  intros. compute. destruct x.
    (* Case y = F1 *)
    dependent destruction y. apply left. auto.
    (* Case y = FS y' *)
    neq.
  (* Case x = FS x' *)
    (* Case y = F1 *)
    dependent destruction y. neq.
    (* Case y = FS y' *)
      (* Case x' = y' *)
      destruct (fin_eq n x y). apply left. rewrite e. auto.
      (* Case x' <> y' *)
      compute in c. neq.
Defined.

Instance EqFin {n} : EqDec (fin n) eq.
  unfold EqDec. intros. apply fin_eq.
Defined.

(* Decidable equality of elements in arbitrary finite sets ('pointed' types) *)
Instance EqFinPt : EqDec {n : nat & fin n} eq.
  unfold EqDec. compute. intros. destruct x. destruct y.
  (* Case x = x0 *)
  destruct (x == x0). compute in e. dependent destruction e.
    (* Case t = t0 *)
    destruct (t == t0). apply left. rewrite e. auto.
    (* Case t <> t0 *)
    compute in c. neq.
  (* Case x <> x0 *)
  compute in c. neq.
Defined.