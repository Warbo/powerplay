(* Useful properties of our Simple.v specification *)
Require Import Simple.

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
        forall {s1 s2 s3},
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
Fixpoint nws_no_worse {D : Domain} {s}
                       n (nws : NoWorseStream s)
      :  NoWorse (get_solver (S n) nws)
                 (get_solver    n  nws)
      := match n,    nws with
             | 0,    nwsCons _ _ p _    => p
             | S n', nwsCons _ _ _ nws' => nws_no_worse n' nws'
         end.

(* All Solvers in a NoWorseStream s are NoWorse than s *)
Theorem get_solver_no_worse {D : Domain} :
        forall s n (nws : NoWorseStream s),
               NoWorse (get_solver n nws)
                        s.
  intros. induction n. destruct nws. simpl.
  exact (no_worse_refl).
  assert (no_worse_next := nws_no_worse n nws).
  apply (no_worse_trans no_worse_next IHn).
Qed.
