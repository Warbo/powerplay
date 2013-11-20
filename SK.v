(* Use SK calculus as a general problem solving framework *)
Require Import EquivDec.
Require Import Omega.
Require Import Program.
Require Import Simple.
Require Import Fin.
Definition fin := Fin.t.

Fixpoint fin_eq {n} (x y : fin n) : {x === y} + {x =/= y}.
  intros. unfold EqDec. intros. compute. destruct x.
  dependent destruction y. apply left. auto.
  apply right. intuition. inversion H.
  dependent destruction y. apply right. intuition. inversion H.
  destruct (fin_eq n x y). apply left. rewrite e. auto.
  apply right. intros. dependent destruction H. compute in c. apply c.
  auto.
Defined.

Instance EqFin {n} : EqDec (fin n) eq.
  unfold EqDec. intros. apply fin_eq.
Defined.

(* Pointed representation *)
Instance EqFinPt : EqDec {n : nat & fin n} eq.
  unfold EqDec. intros. destruct x. destruct y.
  destruct (x == x0). compute in e. dependent destruction e.
  destruct (f == f0). apply left. rewrite e. compute. auto.
  apply right. compute. intro. compute in c. dependent destruction H.
  apply (c eq_refl).
  apply right. compute. intro. dependent destruction H. compute in c.
  apply (c eq_refl).
Defined.

(* Combinators, with meta-language variables *)
Inductive SK : nat -> Type :=
  (* S and K combinators *)
  | cS : forall {n}, SK n
  | cK : forall {n}, SK n
  (* Meta-language variable *)
  | cV : forall {n}, fin n -> SK n
  (* Function application *)
  | cA : forall {n m}, SK n -> SK m -> SK (max n m).

(* Weakening *)
Lemma suc_fin {n} (c : SK (1 + n)) : SK (S n).
  auto.
Defined.

Fixpoint sk_weaken {n} (c : SK n) : SK (S n)
      := match c with
             | cS     => cS
             | cK     => cK
             | cV f   => suc_fin (cV (R 1 f))
             | cA l r => cA (sk_weaken l) (sk_weaken r)
         end.

Fixpoint sk_weaken_n {n m} (c : SK n) : n <= m -> SK m.
  intros. destruct c. exact cS. exact cK.
  rewrite (le_plus_minus n m H). apply cV. rewrite plus_comm.
  apply (R (m - n) f). rewrite <- (Max.max_idempotent m).
  apply (cA (sk_weaken_n n  m c1 (Max.max_lub_l n m0 m H))
            (sk_weaken_n m0 m c2 (Max.max_lub_r n m0 m H))).
Defined.

(* Projection functions *)
(*Definition sk_split {n} (c : SK n) : (SK n * SK n).
  dependent destruction c. exact (cS, cS). exact (cS, cS).
  exact (cS, cS). refine (sk_weaken_n c1 _, sk_weaken_n c2 _).
  apply Max.le_max_l. apply Max.le_max_r.
Defined.

Lemma split_join :
      forall {n m} (l : SK n) (r : SK m),
             sk_weaken_n l (Max.le_max_l n m) = (fst (sk_split (cA l r)))
          /\ sk_weaken_n r (Max.le_max_r n m) = (snd (sk_split (cA l r))).
  intros. simpl. auto.
Qed.

Definition sk_index {n} (c : SK n) := n.
*)
Ltac sk_neq :=
  apply right; intro; dependent destruction H;
  match goal with
        [ c : ?e -> False |- False ] => try (apply (c eq_refl))
  end.

(* Decidable equality of SK combinators, in pointed form *)
Fixpoint sk_eq {n m} (x : SK n) (y : SK m) :
         {existT SK n x === existT SK m y} + {existT SK n x =/= existT SK m y}.
  (* Case n = m *)
  compute. destruct (n == m).
    (* Case x = cS *)
    dependent destruction x.
      (* Case y = cS *)
      destruct y. apply left. rewrite e. auto.
      (* Case y = cK *)
      sk_neq.
      (* Case y = cV f *)
      sk_neq.
      (* Case y = cA y1 y2 *)
      sk_neq.
    (* Case x = cK *)
      (* Case y = cS *)
      destruct y. sk_neq.
      (* Case y = cK *)
      apply left. rewrite e. auto.
      (* Case y = cV f *)
      sk_neq.
      (* Case y = cA y1 y2 *)
      sk_neq.
    (* Case x = cV f *)
      (* Case y = cS *)
      destruct y. rewrite <- e. sk_neq.
      (* Case y = cK *)
      rewrite <- e. sk_neq.
      (* Case y = cV f0 *)
        (* Case f = f0 *)
        destruct (existT fin n f == existT fin n0 f0). compute in e0.
        dependent destruction e0. apply left. auto.
        (* Case f <> f0 *)
        compute in c. sk_neq.
      (* Case y = cA y1 y2 *)
      sk_neq.
    (* Case x = cA x1 x2 *)
      (* Case y = cS *)
      destruct y. sk_neq.
      (* Case y = cK *)
      sk_neq.
      (* Case y = cV f *)
      sk_neq.
      (* Case y = cA y1 y2 *)
        (* Case x1 = y1 *)
        destruct (sk_eq n n0 x1 y1). compute in e0.
        dependent destruction e0.
          (* Case x2 = y2 *)
          destruct (sk_eq m0 m x2 y2). compute in e0.
          dependent destruction e0.
          apply left. auto.
          (* Case x2 <> y2 *)
          compute in c. sk_neq. inversion H.
          dependent destruction H3. apply (c eq_refl).
        (* Case x1 <> y1 *)
        unfold equiv in e. compute in c. sk_neq. inversion H.
        dependent destruction H4. apply (c eq_refl).
  (* Case n <> m *)
  compute. compute in c. sk_neq.
Defined.

Instance SKEqPt : EqDec {n : nat & SK n} eq.
  unfold EqDec. intros. destruct x. destruct y. exact (sk_eq s s0).
Defined.

(* Decidable equality of combinators *)
Instance SKEq {n} : EqDec (SK n) eq.
  unfold EqDec. intros. destruct (sk_eq x y).
  compute in e. dependent destruction e. apply left. compute. auto.
  compute in c. apply right. compute. intro. dependent destruction H.
  apply (c eq_refl).
Defined.

(* Application never reduces an index *)
(*Theorem sk_inc :
        forall {n m} (l : SK n) (r : SK m),
               sk_index l <= sk_index (cA l r) /\
               sk_index r <= sk_index (cA l r).
  intros. unfold sk_index. apply conj.
  apply Max.le_max_l. apply Max.le_max_r.
Qed.
*)

Definition sk_step' {n} (c : SK n) : {m : nat & SK m}
        := match c with
               |     cA (cA cK x) y    => existT SK _ x
               | cA (cA (cA cS x) y) z => existT SK _ (cA (cA x z) (cA y z))
               | _                     => existT SK _ c
           end.

Definition sk_step {n} (c : SK n) : SK n.
  assert (projT1 (sk_step' c) <= n). dependent destruction c.
  auto. auto. auto. simpl. dependent destruction c1.
  auto. auto. auto. dependent destruction c1_1. auto.
  simpl. replace (max n m0) with (max m0 n). rewrite <- Max.max_assoc.
  apply Max.le_max_l. apply Max.max_comm. auto.
  destruct c1_1_1. simpl.
  rewrite <- Max.max_assoc. replace (max m0 m) with (max m m0).
  replace (max m (max m m0)) with (max (max m m) m0).
  rewrite Max.max_idempotent.
  replace (max (max n m1) m0) with (max n (max m1 m0)).
  replace (max (max n (max m1 m0)) m) with (max n (max (max m1 m0) m)).
  replace (max (max m1 m0) m) with (max m1 (max m m0)).
  apply Max.le_max_r. replace (max m m0) with (max m0 m).
  apply Max.max_assoc. apply Max.max_comm.
  apply Max.max_assoc. apply Max.max_assoc.
  rewrite <- Max.max_assoc. auto.
  apply Max.max_comm.
  auto.
  auto.
  auto.
  apply (sk_weaken_n (projT2 (sk_step' c)) H).
Defined.

(* Iteration *)
Fixpoint iterate {m} (c : SK m) n : SK m
      := match n with
             | 0    => c
             | S n' => iterate (sk_step c) n'
         end.

(* Church-encoded booleans: true = \x y. x and false = \x y. y *)
Definition true_in n (c : SK 0) : Prop
        := iterate (cA (cA c (cV     F1  : SK 2))
                             (cV (FS F1) : SK 2)) n = (cV F1 : SK 2).

(* We can encode arbitrary problem domains using combinators *)
Instance skDom : Domain := {
  (* Problems are closed combinators *)
  Problem    := SK 0;
  (* Solutions are (t, a) pairs where (cA p a) reduces to true in t steps *)
  Solution p := {na : nat * SK 0 & true_in (fst na) (cA p (snd na))}
}.

(* We can encode arbitrary problem solvers using combinators *)
Definition sk_default (x : SK 0) (p : Problem) (n : nat)
         : option {na : nat * SK 0 & true_in (fst na) (cA p (snd na))}.
  destruct (iterate (cA (cA (cA p x) (cV     F1  : SK 2))
                                     (cV (FS F1) : SK 2)) n == (cV F1 : SK 2)).
  apply Some. unfold true_in. unfold equiv in e.
  refine (existT _ (n, x) _). auto.
  exact None.
Defined.

Instance skLang : Lang := {
  (* Solvers are written as closed combinators *)
  AST       := SK 0;
  (* We can interpret an AST by applying the problem to it and reducing *)
  interpret := sk_default
}.

Instance skSearcher : GivenSearcher := {
}.