(* Useful properties of our Simple.v specification *)
Require Import Simple.

(* The trivial Solver can't solve any Problem *)
Theorem trivial {D : Domain} :
        forall p n, ~(Solves trivial_solver p n).
  intuition.
Qed.

(* Dominates is transitive *)
Theorem dom_trans {D : Domain} :
        forall {s1 s2 s3},
               Dominates s1 s2 -> Dominates s2 s3 -> Dominates s1 s3.
  (* Break apart our Dominates arguments *)
  intros. destruct H. destruct H0. refine (conj _ _).

  (* Compose their parts *)
  intuition. intuition.
Qed.

(* NoWorse is reflexive *)
Theorem no_worse_refl {D : Domain} :
        forall {s}, NoWorse s s.
  intro. exact (or_intror eq_refl).
Qed.

(* NoWorse is transitive *)
Theorem no_worse_trans {D : Domain} :
        forall s1 s2 s3,
               NoWorse s1 s2 -> NoWorse s2 s3 -> NoWorse s1 s3.
  (* Destruct our NoWorse arguments and solve each case *)
  intros. destruct H. destruct H0.

  (* Dominates s1 s2 /\ Dominates s2 s3 *)
  exact (or_introl (dom_trans H H0)).

  (* Dominates s1 s2 /\ s2 = s3 *)
  rewrite <- H0. exact (or_introl H).

  (* s1 = s2 /\ NoWorse s2 s3 *)
  rewrite H. exact H0.
Qed.

(* The next Solver in a NoWorseStream is NoWorse than the previous *)
CoFixpoint nws_no_worse
Theorem nws_no_worse {D : Domain} :
        forall {s} n (nws : NoWorseStream s),
               NoWorse (get_solver (S n) nws)
                       (get_solver    n  nws)
  intros. destruct n. destruct nws. auto.
  destruct nws. destruct nws. simpl.

(* Solvers in NoWorseStream s are NoWorse than s *)
Theorem get_solver_no_worse_0 {D : Domain} :
        forall s n (nws : NoWorseStream s),
               NoWorse (get_solver n nws)
                       s.
  intros. induction n. destruct nws. simpl.
  exact (no_worse_refl).
  unfold 
Qed.

Theorem get_solver_no_worse_S {D : Domain} :
        forall s (nws : NoWorseStream s) n,
               NoWorse (get_solver (S n) nws)
                       (get_solver    n  nws).
  intros. induction n. destruct nws. auto.
  destruct nws. simpl. IHn. simpl. destruct nws.
  unfold NoWorse. destruct nws. get_solver.