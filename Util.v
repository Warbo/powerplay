(* Utility functions *)
Require Import Program.

Inductive Iso (a b : Type) : Type :=
  | iso : forall (ab  : a -> b)
                 (ba  : b -> a)
                 (aba : forall x, ab (ba x) = x)
                 (bab : forall x, ba (ab x) = x),
                 Iso a b.
Arguments iso [a b] ab ba aba bab.

Definition swapIso (a b : Type)
                   (i   : Iso a b)
                        : Iso b a
        := match i with
               | iso ab ba aba bab => iso ba ab bab aba
           end.
Arguments swapIso [a b] i.

Definition castA (a b : Type) (i : Iso a b) : a -> b
        := match i with
               | iso ab _ _ _ => ab
           end.
Arguments castA [a b] i _.

Definition castB (a b : Type) (i : Iso a b) : b -> a
        := match i with
               | iso _ ba _ _ => ba
           end.
Arguments castB [a b] i _.

Definition uwa : forall a b (i : Iso a b)
                        f x,
                        f x -> f (castB i (castA i x)).
  intros. destruct i. simpl. rewrite (bab x). auto.
Defined.
Arguments uwa [a b] i f x _.

Definition uwb : forall a b (i : Iso a b)
                        f x,
                        f (castB i (castA i x)) -> f x.
  intro. intro. intro. intro. intro. destruct i. simpl.
  rewrite (bab x). exact id.
Defined.
Arguments uwb [a b] i f x _.

Definition uwa' : forall a b (i : Iso a b)
                         f x,
                         f x -> f (castA i (castB i x)).
  intros. unfold castA. unfold castB. destruct i. rewrite aba. auto.
Defined.
Arguments uwa' [a b] i f x _.

Definition uwb' : forall a b (i : Iso a b)
                         f x,
                         f (castA i (castB i x)) -> f x.
  intros. unfold castA in X. unfold castB in X. destruct i.
  rewrite aba in X. auto.
Defined.
Arguments uwb' [a b] i f x _.

Definition iso_f (a b : Type)
                 (i   : Iso a b)
                 (f   : a -> Type)
                 (x   : a)
                      : Iso (f x) (f (castB i (castA i x))).
  refine (iso (uwa i f x) (uwb i f x) _ _). intro.

  unfold uwa. unfold uwb. destruct i. unfold eq_rect_r.
  destruct (bab x). compute. auto.

  intro. unfold uwb. unfold uwa. destruct i. unfold eq_rect_r.
  rewrite (bab x). compute. auto.
Defined.
Arguments iso_f [a b] i f x.

Definition optionMap (i o : Type) (x : option i) (f : i -> o) : option o
        := match x with
               | None    => None
               | Some x' => Some (f x')
           end.
Arguments optionMap [i o] x f.

Theorem optionMapComposes :
        forall a b c (f : a -> b) (g : b -> c) x,
               optionMap (optionMap x f) g = optionMap x (compose g f).
  intros. unfold optionMap. destruct x. unfold compose. auto. auto.
Qed.
Arguments optionMapComposes [a b c] f g x.
