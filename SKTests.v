(* Unit tests and theorems about SK.v *)
Require Import SK.
Require Import SKUtil.

(* Measures *)
Theorem sk_sizeT1 : sk_size cS = 1.
  auto.
Qed.

Theorem sk_sizeT2 l r : sk_size (cA l r) = sk_size l + sk_size r.
  auto.
Qed.

Theorem sk_maxT1 c : sk_max (sk_step c) <= sk_max c.
  induction c; [auto..]. induction c1; [auto..].
  induction c1_1; [auto..]. simpl. apply Max.le_max_l.
  destruct c1_1_1; [auto..]. simpl.
  max_le.
Qed.

(* Equality *)
Theorem sk_eq_refl (c : SK) : c === c.
  destruct (c == c); [deqs..].
Qed.

Theorem sk_eq_trans (a b c : SK) : a === b -> b === c -> a === c.
  ddeqs.
Qed.

(* Beta reduction *)
Theorem sk_step_K : forall x y, sk_step (cA (cA cK x) y) = x.
  auto.
Qed.

Theorem sk_step_S : forall x y z,
                           sk_step (cA (cA (cA cS x) y) z) = cA (cA x z) (cA y z).
  auto.
Qed.

Theorem sk_stepT2 : forall x, ~(exists y z, x = cA y z) -> sk_step x = x.
  intuition. induction x; [auto..]. destruct H. exists x1 x2. auto.
Qed.

(* Meta-programming *)
Theorem sk_apply_to_0 c : sk_apply_to c 0 = c.
  auto.
Qed.

Theorem sk_apply_to_S c n : sk_apply_to c (S n) = cA (sk_apply_to c n)
                                                     (cV (S n)).
  auto.
Qed.
