(* Implementation of SK combinator calculus *)
Require Import Omega.
Require Import SKUtil.
Require Import Program.

(* Combinators, with meta-language variables *)
Inductive SK : Type :=
  (* S and K combinators *)
  | cS : SK
  | cK : SK
  (* Meta-language variable *)
  | cV : nat -> SK
  (* Function application *)
  | cA : SK -> SK -> SK.

(* Simple measures *)
Fixpoint sk_size c : nat
  := match c with
         | cS     => 1
         | cK     => 1
         | cV _   => 1
         | cA l r => sk_size l + sk_size r
     end.

(* Decidable equality of SK combinators *)
Program Fixpoint sk_eq (x y : SK) : {x === y} + {x =/= y}
  := match x,        y        with
         | cS,       cS       => left _
         | cK,       cK       => left _
         | cV n,     cV m     => match n == m with
                                     | left  _ => left  _
                                     | right _ => right _
                                 end
         | cA l1 r1, cA l2 r2 => match sk_eq l1 l2, sk_eq r1 r2 with
                                     | left _, left _ => left _
                                     | _,      _      => right _
                                 end
         | _,        _        => right _
     end.

Next Obligation. Proof.
  destruct (H eq_refl eq_refl). auto.
Defined.

Next Obligation. Proof.
  dependent destruction y.
    apply H3. auto.
    apply H. auto.
    apply (H1 n n). auto.
    apply (H2 y1 y2 y1 y2). auto.
Qed.

Ltac sk_tac := unfold complement, equiv; program_simpl; deqs.
Solve Obligations with sk_tac.

Instance SKEq : EqDec SK eq := sk_eq.

(* Beta reduction *)
Program Definition sk_step (c : SK) : SK
  := match c with
         |     cA (cA cK x) y    => x
         | cA (cA (cA cS x) y) z => cA (cA x z) (cA y z)
         | _                     => c
     end.

Solve Obligations with sk_tac.

Fixpoint iterate (c : SK) n : SK
      := match n with
             | 0    => c
             | S n' => iterate (sk_step c) n'
         end.

(* Find SK terms which reduce to a given term when applied to variables *)


(* Finds the largest variable number in an SK term *)
Fixpoint sk_max (c : SK) : nat
  := match c with
         | cS     => 0
         | cK     => 0
         | cV m   => m
         | cA l r => max (sk_max l) (sk_max r)
     end.

(* Apply a term to n arguments *)
Fixpoint sk_apply_to' (c : SK) n m : SK
  := match n, m with
         | 0, _    => c
         | _, 0    => c
         | _, S m' => sk_apply_to' (cA c (cV (n - m'))) n m'
     end.
Definition sk_apply_to c n := sk_apply_to' c n n.

Theorem skat1 c : sk_apply_to c 4 = cA (cA (cA (cA c
                                                   (cV 1))
                                               (cV 2))
                                           (cV 3))
                                       (cV 4).
  auto.
Qed.

Theorem skat2 c : sk_apply_to c 0 = c.
  auto.
Qed.
Print lt_dec.
(* Abstract the variables out of a combinator *)
Program Fixpoint sk_abstract (c : SK)
  := let m := sk_max c in
     match c with
         | cV _        => c (* Can't abstract *)
         | cA l (cV n) => match lt_dec (sk_max l) m, m == n with
                              | left _, left _ => 
                              | _,      _      => 

Program Fixpoint sk_find (c : SK) n : option SK
  := sk_apply_to c (sk_max c)

(* Church-encoding of SK terms *)
Program Fixpoint sk_quote (c : SK) : SK
  := match c with
                     (* "S" a b c = a *)
         | cS     => cA (cA cS (cA cK cK)) cK
                     (* "K" a b c = b *)
         | cK     => cA cK cK
                     (* "l r" a b c = c "l" "r" *)
         | cA l r => cA cK
                       (cA cK
                          (cA (cA cS
                                 (cA (cA cS (cA (cA cS cK) cK))
                                            (cA cK (sk_quote l))))
                                 (cA cK (sk_quote r))))
         | cV n   => cV n
     end.

(* Unquote terms:
 * U 'S' = S
 *       = 'S' S b c
 * We can unquote 'S' by passing it an S and (any) two other combinators.
 *
 * U 'K' = K
 *       = 'K' a K c
 * We can unquote 'K' by passing it any combinator, K and any combinator.
 *
 * U 'l r' = l r
 *         = 'l r' a b C, for some C
 *         = C 'l' 'r'
 *         = (U 'l') (U 'r')
 *
 * This is tricky, since U is recursive: it must be Y X for some
 * non-recursive X and fixpoint combinator Y:
 *
 * X u 'l r' = (u 'l') (u 'r') 
 *           = C 'l' 'r'
 *           = D u 'l' 'r', for some D
 *
 * Finding D is simple, but tedious:
 *
 *   D x y z = (x y) (x z)
 *           = K (x y) z (x z)
 *           = S (K (x y)) x z
 *
 *     D x y = S (K (x y)) x
 *           = S (K (I (x y))) x, where I x = x
 *           = S (K (K I y (x y))) x
 *           = S (K (S (K I) x y)) x
 *           = S ((K K y) (S (K I) x y)) x
 *           = S (S (K K) (S (K I) x) y) x
 *           = (K S y) (S (K K) (S (K I) x) y) x
 *           = S (K S) (S (K K) (S (K I) x)) y x
 *           = S (K S) (S (K K) (S (K I) x)) y (K x y)
 *           = S (S (K S) (S (K K) (S (K I) x))) (K x) y
 *
 *       D x = S (S (K S) (S (K K) (S (K I) x))) (K x)
 *           = S (S (K S) (K (S (K K)) x (S (K I) x))) (K x)
 *           = S (S (K S) (S (K (S (K K))) (S (K I)) x)) (K x)
 *           = S (K (S (K S)) x (S (K (S (K K))) (S (K I)) x)) (K x)
 *           = S (S (K (S (K S))) (S (K (S (K K))) (S (K I))) x) (K x)
 *           = (K S x) (S (K (S (K S))) (S (K (S (K K))) (S (K I))) x) (K x)
 *           = S (K S) (S (K (S (K S))) (S (K (S (K K))) (S (K I)))) x (K x)
 *           = S (S (K S) (S (K (S (K S))) (S (K (S (K K))) (S (K I))))) K x
 *
 *         D = S (S (K S) (S (K (S (K S))) (S (K (S (K K))) (S (K I))))) K
 *
 * Hence:
 *
 *    U 'l r' = Y X 'l r' = 'l r' a b (D (Y X)), so c = D (Y X)
 *
 *    U x = x S K (D (Y X))
 *
 *)
Program Fixpoint sk_unquote (c c' : SK) (p : sk_quote c' = c) : SK
  := let Y := cA (cA (cA cS cS) cK)
                (cA (cA (cA cS (cA cK (cA (cA cS cS) (cA cS (cA (cA cS cS) cK))))) cK)) in
Y.
     let X = 
     let C = cA D (cA Y X) in
         cA (cA (cA c cS) cK) C


(* 'S' = \xyz. x *)
Definition s_enc := cA cK cV 1.
Definition k_enc := cA cK cV 2.
Definition a_enc := cA.
Definition is_S x n := iterate (cA (cA (cA x (cV 1)) (cV 2)) (cV 3)) n = cV 1.

(* 'K' = \xyz. y *)
Definition is_K x n := iterate (cA (cA (cA x (cV 1)) (cV 2)) (cV 3)) n = cV 2.

(* 'A' = \xyz. z*)
Definition is_A x n := iterate (cA (cA (cA x (cV 1)) (cV 2)) (cV 3)) n = cV 3.
(*  *)

Lemma sk_size_S c : exists n, sk_size c = S n.
  induction c; match goal with
                   | [ |- context[cA] ] => idtac
                   | [ |- _           ] => eapply ex_intro; simpl; auto
               end.
  destruct IHc1. destruct IHc2. simpl. ddeqs.
  simpl. exists (x + S x0). auto.
Qed.

Fixpoint sk_max (c : SK) : nat
  := match c with
         | cS     => 0
         | cK     => 0
         | cV m   => m
         | cA l r => max (sk_max l) (sk_max r)
     end.

(* Decidable equality of SK combinators *)
Program Fixpoint sk_eq (x y : SK) : {x === y} + {x =/= y}
  := match x,        y        with
         | cS,       cS       => left _
         | cK,       cK       => left _
         | cV n,     cV m     => match n == m with
                                     | left  _ => left  _
                                     | right _ => right _
                                 end
         | cA l1 r1, cA l2 r2 => match sk_eq l1 l2, sk_eq r1 r2 with
                                     | left _, left _ => left _
                                     | _,      _      => right _
                                 end
         | _,        _        => right _
     end.

Next Obligation. Proof.
  destruct (H eq_refl eq_refl). auto.
Defined.

Next Obligation. Proof.
  dependent destruction y.
    apply H3. auto.
    apply H. auto.
    apply (H1 n n). auto.
    apply (H2 y1 y2 y1 y2). auto.
Qed.

Solve Obligations with sk_tac.

Instance SKEq : EqDec SK eq := sk_eq.

(* Beta reduction *)
Program Definition sk_step (c : SK) : SK
  := match c with
         |     cA (cA cK x) y    => x
         | cA (cA (cA cS x) y) z => cA (cA x z) (cA y z)
         | _                     => c
     end.

Solve Obligations with sk_tac.

Definition normal c := sk_step c = c.

Fixpoint iterate (c : SK) n : SK
      := match n with
             | 0    => c
             | S n' => iterate (sk_step c) n'
         end.

(* Apply a term to n arguments *)
Fixpoint sk_apply_to (c : SK) n : SK
  := match n with
         | 0    => c
         | S n' => cA (sk_apply_to c n') (cV n)
     end.

(* Abstract the variables out of a combinator *)
Program Fixpoint sk_abstract' (c : SK) (a : nat)
  : option SK
  := let m := sk_max c in
     match a, m, c with
         | 0,    _, _           => None (* Stop recursing *)
         | _,    0, _           => None (* Nothing to abstract *)
         | _,    _, cV _        => None (* Can't abstract *)
         | S a', _, cA l (cV n) => match lt_dec (sk_max l) m, m == n with
                                       | left _, left _ => Some l
                                       | _,      _      => sk_abstract' c a'
                                   end
         | S a', _, cA l r      => match sk_abstract' l a', sk_abstract' r a' with
                                       | Some l', Some r' => Some (cA l' r')
                                       | Some l', None    => Some (cA l' r )
                                       | None,    Some r' => Some (cA l  r')
                                       | None,    None    => None
                                   end
         | _,    _, _           => !
     end.

Next Obligation. Proof.
  intuition. induction c.
    refine (H _ _ _). intuition.
    refine (H _ _ _). intuition.
    refine (H0 _ _ _ _). intuition.
    refine (H2 (pred a) _ _ _ _). intuition. destruct a.
      destruct (H3 (sk_max (cA c1 c2)) (cA c1 c2)). intuition.
      auto.
Qed.

Next Obligation. Proof.
  intuition; try inversion H4.
Defined.

Next Obligation. Proof.
  intuition; inversion H4.
Defined.

Next Obligation. Proof.
  intuition.
Defined.

Next Obligation. Proof.
  intuition. inversion H3.
Defined.

Next Obligation. Proof.
  intuition. inversion H3.
Defined.

Next Obligation. Proof.
  intuition. inversion H5.
Defined.

Definition sk_abstract c := sk_abstract' c (sk_size c).

(*
Program Fixpoint sk_find (c : SK) n : option SK
  := sk_apply_to c (sk_max c).
*)
(* Church-encoding of SK terms *)
(*
Program Fixpoint sk_quote (c : SK) : SK
  := match c with
                     (* "S" a b c = a *)
         | cS     => cA (cA cS (cA cK cK)) cK
                     (* "K" a b c = b *)
         | cK     => cA cK cK
                     (* "l r" a b c = c "l" "r" *)
         | cA l r => cA cK
                       (cA cK
                          (cA (cA cS
                                 (cA (cA cS (cA (cA cS cK) cK))
                                            (cA cK (sk_quote l))))
                                 (cA cK (sk_quote r))))
         | cV n   => cV n
     end.
*)
(* Unquote terms:
 * U 'S' = S
 *       = 'S' S b c
 * We can unquote 'S' by passing it an S and (any) two other combinators.
 *
 * U 'K' = K
 *       = 'K' a K c
 * We can unquote 'K' by passing it any combinator, K and any combinator.
 *
 * U 'l r' = l r
 *         = 'l r' a b C, for some C
 *         = C 'l' 'r'
 *         = (U 'l') (U 'r')
 *
 * This is tricky, since U is recursive: it must be Y X for some
 * non-recursive X and fixpoint combinator Y:
 *
 * X u 'l r' = (u 'l') (u 'r')
 *           = C 'l' 'r'
 *           = D u 'l' 'r', for some D
 *
 * Finding D is simple, but tedious:
 *
 *   D x y z = (x y) (x z)
 *           = K (x y) z (x z)
 *           = S (K (x y)) x z
 *
 *     D x y = S (K (x y)) x
 *           = S (K (I (x y))) x, where I x = x
 *           = S (K (K I y (x y))) x
 *           = S (K (S (K I) x y)) x
 *           = S ((K K y) (S (K I) x y)) x
 *           = S (S (K K) (S (K I) x) y) x
 *           = (K S y) (S (K K) (S (K I) x) y) x
 *           = S (K S) (S (K K) (S (K I) x)) y x
 *           = S (K S) (S (K K) (S (K I) x)) y (K x y)
 *           = S (S (K S) (S (K K) (S (K I) x))) (K x) y
 *
 *       D x = S (S (K S) (S (K K) (S (K I) x))) (K x)
 *           = S (S (K S) (K (S (K K)) x (S (K I) x))) (K x)
 *           = S (S (K S) (S (K (S (K K))) (S (K I)) x)) (K x)
 *           = S (K (S (K S)) x (S (K (S (K K))) (S (K I)) x)) (K x)
 *           = S (S (K (S (K S))) (S (K (S (K K))) (S (K I))) x) (K x)
 *           = (K S x) (S (K (S (K S))) (S (K (S (K K))) (S (K I))) x) (K x)
 *           = S (K S) (S (K (S (K S))) (S (K (S (K K))) (S (K I)))) x (K x)
 *           = S (S (K S) (S (K (S (K S))) (S (K (S (K K))) (S (K I))))) K x
 *
 *         D = S (S (K S) (S (K (S (K S))) (S (K (S (K K))) (S (K I))))) K
 *
 * Hence:
 *
 *    U 'l r' = Y X 'l r' = 'l r' a b (D (Y X)), so c = D (Y X)
 *
 *    U x = x S K (D (Y X))
 *
 *)
(*
Program Fixpoint sk_unquote (c c' : SK) (p : sk_quote c' = c) : SK
  := let Y := cA (cA (cA cS cS) cK)
                (cA (cA (cA cS (cA cK (cA (cA cS cS) (cA cS (cA (cA cS cS) cK))))) cK)) in
Y.
     let X =
     let C = cA D (cA Y X) in
         cA (cA (cA c cS) cK) C
*)

(* 'S' = \xyz. x *)
Definition s_enc := cA cK (cV 1).
Definition k_enc := cA cK (cV 2).
Definition a_enc := cA.
Definition is_S x n := iterate (cA (cA (cA x (cV 1)) (cV 2)) (cV 3)) n = cV 1.

(* 'K' = \xyz. y *)
Definition is_K x n := iterate (cA (cA (cA x (cV 1)) (cV 2)) (cV 3)) n = cV 2.

(* 'A' = \xyz. z*)
Definition is_A x n := iterate (cA (cA (cA x (cV 1)) (cV 2)) (cV 3)) n = cV 3.
(*
Definition sk_interpret (solver : SK 0) (problem : Problem) (n : nat)
         : option {a : SK 0 & true_in (snd problem) (cA (fst problem) a)}.
  set (answer := cA solver (fst problem)).
  destruct (iterate (cA (cA (cA (fst problem) answer)
                            (cV     F1  : SK 2))
                            (cV (FS F1) : SK 2))
                    (snd problem) == (cV F1 : SK 2)).
  apply Some. unfold true_in. unfold equiv in e.
  refine (existT _ answer _). auto.
  exact None.
Defined.

(* We can encode arbitrary problem domains using combinators and timeouts *)
Instance skDom : Domain := {
  (* Problems are closed boolean decision procedures *)
  Problem    := SK 0 * nat;
  (* Solutions are (t, a) pairs where (cA p a) reduces to true in t steps *)
  Solution p := {a : SK 0 & true_in (snd p) (cA (fst p) a)}
}.

Instance skLang : Lang := {
  (* Solvers are written as closed combinators *)
  AST       := SK 0;
  (* We can interpret an AST by applying the problem to it and reducing *)
  interpret := sk_interpret
}.

(* We can use Problems to distinguish between Solvers *)
Definition solver_diff s1 s2 n
        := {p : Problem | Solves (sk_interpret s1) p n /\
                        ~(Solves (sk_interpret s2) p n)}.

(* We can combine two distinguishable Solvers to make one which Dominates *)
Lemma bolt_on {s1 s2 n}
    : solver_diff s1 s2 n ->
      {s3 : SK 0 | forall p m,
                          (Solves (sk_interpret s1) p m ->
                           Solves (sk_interpret s3) p m) /\
                          (Solves (sk_interpret s2) p m ->
                           Solves (sk_interpret s3) p (n + m))}.
  intros. destruct X. destruct a.
  \f g p. (p (f p)) (f p) (g p)

refine (exist _ _ _).
  intros. apply conj. intro.
  unfold Solves.
  assert {s3 : SK 0 |
          forall p m,
                 Solves s1 p n -> Solves s3 p n}. eapply ex_intro.
  unfold Dominates. apply conj. intros. apply H. destruct H.

(* List all combinators of a given size *)
Fixpoint decode_all n := match n with
| 0 => []
| 1 => [cS ; cK]

Instance skSearcher : GivenSearcher := {
}.
*)