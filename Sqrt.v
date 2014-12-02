(* A straightforward, non-recursive PowerPlay implementation *)
Require Import EquivDec.
Require Import NPeano.

(* We'll implement the Simple specification to find square roots *)
Require Import Simple.

(* The square root of a number *)
Inductive Sqrt : nat -> Type :=
  sqrt : forall n, Sqrt (n * n).

(* Our Domain is turning Naturals into their Sqrts *)
Instance SqrtDom : Domain := {
  Problem  := nat;
  Solution := Sqrt
}.

(* We implement a simple Language of hard-coded answers *)
Inductive SqrtList : Type :=
  | sqrtNil  : SqrtList
  | sqrtCons : forall n, Sqrt n -> SqrtList -> SqrtList.

Lemma srl_convert {n m} : n === m -> Sqrt n -> Sqrt m.
  intros. rewrite <- H. auto.
Defined.

(* We can find a Sqrt if it's in a SqrtList *)
Fixpoint sqrt_interpret (l : SqrtList) p (n : nat)
      := match l return option (Sqrt p) with
             | sqrtNil          => None
             | sqrtCons p' s l' => match p' == p with
                                      | left r  => Some (srl_convert r s)
                                      | right _ => sqrt_interpret l' p n
                                  end
         end.

(* SqrtList will be our implementation Language *)
Instance SqrtLang : Lang := {
  AST       := SqrtList;
  interpret := sqrt_interpret
}.

(* Now we define a Searcher *)

(* Proof that a number is in an SqrtList *)
Inductive InSRL : nat -> SqrtList -> Prop :=
  | srlHead : forall {n} h t, InSRL n (sqrtCons n h t)
  | srlTail : forall {n m} h t, InSRL n t -> InSRL n (sqrtCons m h t).

(* Membership is decidable *)
Lemma in_srl_dec n l : InSRL (square n) l + ~(InSRL (square n) l).
  induction l. apply inr. intro. inversion H.
  destruct (square n == n0). apply inl. rewrite e. apply srlHead.
  destruct IHl. apply inl. apply srlTail. auto.
  apply inr. intro. assert (~(square n = n0)). intro. rewrite H0 in c.
  compute in c. exact (c eq_refl). apply H0. inversion H. auto.
  assert (f := n1 H3). inversion f.
Defined.

(* Try to find a number that's not in a list by counting down from n *)
Fixpoint le_not_in_srl (n : nat) l : option {m | ~InSRL (square m) l}.
  destruct n. exact None.
  destruct (in_srl_dec n l). exact (le_not_in_srl n l).
  apply Some. apply (exist _ n n0).
Defined.

(* If a number's not in a list, that list can't solve that number *)
Lemma not_in_means_unsolvable n m l
    : ~InSRL n l -> sqrt_interpret l n m = None.
  unfold not. intro. induction l. auto.
  simpl. destruct (equiv_dec n0 n). assert False. apply H.
  rewrite <- e. apply srlHead. inversion H0. 
  apply IHl. intros. apply H. compute in c. apply srlTail. auto.
Qed.

(* Prepend a number to a list, if we can find one that's not already there *)
Fixpoint sqrt_searcher ast1 :
         nat -> option {ast2 | Dominates (interpret ast2)
                                         (interpret ast1)}.
  (* Case le_not_in_srl H ast1 = Some s *)
  intros. destruct (le_not_in_srl H ast1). destruct s. apply Some.
  refine (exist _ (sqrtCons (square x) (sqrt x) ast1) _).

  (* Prove that existing problems are still solved *)
  unfold Dominates. apply conj. intros. unfold Solves in H0. simpl in H0.
  unfold Solves. unfold not. intro. simpl in H1.
  destruct (equiv_dec (square x) p). inversion H1.
  rewrite H1 in H0. apply (H0 eq_refl).

  (* Prove that the new problem was unsolvable *)
  unfold not. intros. assert (q := H0 (square x) 0). unfold Solves in q.
  simpl in q. destruct (equiv_dec (square x) (square x)). apply q.
  intro. inversion H1. apply not_in_means_unsolvable. auto.
  apply c. constructor.

  (* Case le_not_in_srl H ast1 = None *)
  exact None.
Defined.

(* Build our PowerPlay implementation *)
Instance SqrtSearcher : GivenSearcher := {
  searcher := sqrt_searcher
}.

Definition sqrt_powerplay : NoWorseStream (interpret sqrtNil)
        := powerplay SqrtDom SqrtLang SqrtSearcher sqrtNil.
