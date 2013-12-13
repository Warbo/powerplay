(* A very useful library *)
Require Export Program.
Require Import Max.

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

(* Solves a False goal if we have bogus equalities *)
Ltac destruct_eq :=
  match reverse goal with
      | [ H : _ = _   |- _ ] =>               inversion H; clear H
      | [ H : _ === _ |- _ ] => compute in H; inversion H; clear H
  end.

Ltac ddestruct_eq :=
  match reverse goal with
      | [ H : _ = _   |- _ ] =>               rewrite H in *; clear H
      | [ H : _ === _ |- _ ] => compute in H; rewrite H in *; clear H
  end.

Ltac deqs  := intuition; repeat destruct_eq.

Ltac ddeqs := intuition; repeat ddestruct_eq; intuition.

Theorem deqsT1 : forall n, (1 = 1)     ->
                           (2 = 3)     ->
                           (S n = S n) ->
                          ~(4 = 4 /\ 5 = 5).
  deqs.
Qed.

Theorem deqsT2 : (0 === 1) -> False.
  deqs.
Qed.

Theorem ddeqsT1 : forall A (a b c : A), (a = b) -> (b = c) -> (a = c).
  ddeqs.
Qed.

Ltac max_le := repeat (
  match goal with
      (* Annihilate repeated values *)
      | [ |- context[max ?X          ?X         ] ] => rewrite    (max_idempotent X)

      (* Propagate repeated values to the left *)
      | [ |- context[max ?X          (max ?Y ?X)] ] => rewrite    (max_comm  Y X)
      | [ |- context[max ?X          (max ?X ?Y)] ] => rewrite    (max_assoc X X Y)
      | [ |- context[max (max _  ?X) (max ?Y ?X)] ] => rewrite    (max_comm  Y X)
      | [ |- context[max (max ?X ?Y) (max ?Y _ )] ] => rewrite    (max_comm  X Y)
      | [ |- context[max (max ?X ?Y) (max ?X ?Z)] ] => rewrite <- (max_assoc X Y (max X Z))
      | [ |- context[max ?X (max ?Y (max ?X ?Z))] ] => rewrite    (max_assoc Y X Z)
      | [ |- context[max ?X (max (max ?X ?Y) ?Z)] ] => rewrite    (max_assoc X (max X Y) Z)
      | [ |- context[max ?X (max (max ?Y ?X) ?Z)] ] => rewrite    (max_assoc X (max Y X) Z)

      (* Rearrange permutations *)
      (* max (max y x) z <= max (max x z) y *)
      | [ |- max (max ?X ?Y) ?Z <= max (max ?Y ?Z) ?X ] => rewrite <- (max_assoc X Y Z)
      | [ |- max ?X          ?Y <= max ?Y          ?X ] => rewrite    (max_comm  X Y)
  end; auto).

Theorem max_leT1 x y z : max (max x y) (max z y) <= max (max x z) y.
  max_le.
Qed.

Theorem max_leT2 x : max (max (max x x) x) (max x x) = x.
  max_le.
Qed.
