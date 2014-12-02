(* Implements a dependently-typed language *)

(* Drag in our dependencies *)
Require Import Bool.
Require Import Coq.Classes.EquivDec.
Require Import Coq.Program.Equality.
Require Import Omega.
Require Import Vector.
Require Import Fin.
Definition Vec := Vector.t.
Definition F   := Fin.t.

(* Raw terms. Warning: These can be ill-formed! *)
Inductive cT : Type :=
  | cType   : nat -> cT       (* Type with universe index    *)
  | cVar    : nat -> cT       (* de Bruijn index             *)
  | cEmpty  : cT              (* Empty type                  *)
  | cUnit   : cT              (* Trivial type                *)
  | cNull   : cT              (* cUnit introduction          *)
  | cMu     : cT              (* Recursive type combinator   *)
  | cFold   : cT              (* Recursive type introduction *)
  | cUnfold : cT              (* Recursive type elimination  *)
  | cPi     : cT -> cT -> cT  (* Dependent function type     *)
  | cLam    : cT -> cT        (* Dependent function value    *)
  | cSig    : cT -> cT -> cT  (* Dependent pair type         *)
  | cPair   : cT              (* Dependent pair introduction *)
  | cFst    : cT              (* Dependent pair elimination  *)
  | cSnd    : cT              (* Dependent pair elimination  *)
  | cApp    : cT -> cT -> cT  (* Function application        *).

(* Substitute x for 'Var n' in t *)
Fixpoint subst (n   : nat)
               (x t : cT)
                    : cT
      := match t with
             | cVar  m   => if m == n then x else t
             | cSig  i o => cSig  (subst    n  x i)
                                  (subst (S n) x o)
             | cPi   i o => cPi   (subst    n  x i)
                                  (subst (S n) x o)
             | cLam  b   => cLam  (subst (S n) x b)
             | cApp  l r => cApp  (subst (S n) x l)
                                  (subst    n  x r)
             | _         => t
         end.

(* One beta-reduction step (bool indicates progress) *)
Fixpoint cStep (t : cT) : (cT * bool) :=
  match t with
      (* Functions are applied to their arguments *)
      | cApp (cLam f) x => (subst 0 x f, true)
      | cApp cFst (cApp (cApp cPair l) r) => (l, true)
      | cApp cSnd (cApp (cApp cPair l) r) => (r, true)
      | cApp cUnfold (cApp cFold x)       => (x, true)

      (* Beta reduction trickles down the AST *)
      | cSig  x y => let (x', xb) := cStep x in
                     let (y', yb) := cStep y in
                         (cSig x' y', orb xb yb)
      | cPi   i o => let (i', ib) := cStep i in
                     let (o', ob) := cStep o in
                         (cPi i' o', orb ib ob)
      | cLam  b   => let (b', ob) := cStep b in
                         (cLam b', ob)
      | cApp  f x => let (x', xb) := cStep x in
                     let (f', fb) := cStep f in
                         (cApp f' x', orb fb xb)

      (* Everything else is in normal form *)
      | _ => (t, false)
  end.

(* Multiple steps of beta-reduction *)
Fixpoint cSteps (n : nat) (t : cT) : cT
      := match n with
             | 0   => t
             | S m => match cStep t with
             | (t', false) => t'
             | (t', true)  => cSteps m t'
         end end.

(* Asserts that a term normalises in n steps *)
Fixpoint stepCount (n : nat) (t : cT) : Prop :=
  match cStep t with
      | (_, false) => True
      | (t', true) => match n with
                          | 0   => False
                          | S m => stepCount m t'
                      end
  end.

(* Asserts that a term is in normal form *)
Definition normal := stepCount 0.

(* Asserts that two terms are beta-equivalent *)
Definition betaEquiv (a b : cT) : Prop
        := exists c n m, cSteps n a = c /\ cSteps m b = c.

(* Some commonly used typing assertions. Note that these need to be
 * 'instantiated' with a typing predicate to prevent digergence.
 *)

(* anyType' f t asserts that t : cType m, for some m *)
Definition anyType' (f : cT -> cT -> Prop)
                    (t : cT)
                       : Prop
        := exists m, f (cType m) t.

(* lowerType' f n t asserts that t : cType m, for some m < n *)
Definition lowerType' (f : cT -> cT -> Prop)
                      (n : nat)
                      (t : cT)
                         : Prop
        := exists m, f (cType m) t /\ m < n.

(* Asserts that trm : typ. Ill-formed terms or types will result in
 * False, which is unprovable. "a" is a hack to ensure termination.
 *)
Fixpoint cTyped (a len   : nat)
                (ctx     : Vec cT len)
                (typ trm : cT)
                         : Prop :=
  match a with
      (* We've run out of recursion. Give up. *)
      | 0   => False

      (* We can recurse. Instantiate some common idioms: *)
      | S b => (* typedHere x y asserts that y : x *)
               let typedHere          := cTyped b len ctx in

               (* typedWith x y z asserts that z : y, given Var 0 : x *)
               let typedWith (t : cT) := cTyped b (S len)
                                                (cons cT t len ctx) in

               (* anyType t asserts that t : cType m for some m *)
               let anyType            := anyType' typedHere in

               (* lowerType n t asserts that t : cType m for some m < n *)
               let lowerType          := lowerType' typedHere in

  match trm, typ with
        (* cEmpty is always a type *)
      | cEmpty, cType _ => True

        (* cUnit is always a type *)
      | cUnit, cType _ => True

        (* cNull is always a cUnit *)
      | cNull, cUnit => True

        (* Types are stratified to prevent paradoxes *)
      | cType m, cType n => m < n

        (* Dependent pair is a type if its paramters are valid *)
      | cSig i o, cType n =>

        (* i : cType m, where m < n *)
        lowerType n i

        (* o : cPi i (cType m), where m < n *)
        /\ (exists m, typedHere (cPi i (cType m)) o /\ m < n)

        (* Dependent function is a type if its paramters are valid *)
      | cPi i o, cType n =>

        (* i : cType m, where m < n *)
        lowerType n i

        (* o : cPi i (cType m), where m < n *)
        /\ (exists m, typedHere (cPi i (cType m)) o /\ m < n)

        (* Application requires the function and argument to match too *)
      | cApp f x, t =>

        (* t : cType m, for some m *)
        anyType t

        (* Introduce some i and o *)
        /\ (exists i o, (* f : cPi i o *)
                        (typedHere (cPi i o) f)

                        (* x : i *)
                        /\ (typedHere i x)

                        (* i : Type m, for some m *)
                        /\ anyType i

                        (* o x reduces to t *)
                        /\ (betaEquiv t (cApp o x)))

      | cFst,       cPi (cSig l r) o  =>
        betaEquiv l o

      | cSnd,       cPi (cSig l r) o  =>
        betaEquiv r o

      | cLam b,     cPi i o           =>
        inhabited (forall x, typedWith i (cApp o x) (subst 0 x b))

        (* We must have enough context to look up a variable's type and it must be
         * equivalent to t. *)
      | cVar n, t => exists (p : n < len), betaEquiv (nth ctx (of_nat_lt p)) t

      | cPair, cPi l o =>
        exists r,
               betaEquiv o (cPi r (cSig l r))

      | _,           _                =>
        False
  end end.

(* Nothing is typeable without recursion *)
Theorem need_recursion : forall n c t1 t2,
                              ~(cTyped 0 n c t1 t2).
  intros. unfold not. intro. destruct H.
Qed.

(* Allowing more recursion does not decrease what we can prove *)
(*
Theorem more_recursion : forall r n c t1 t2,
                                cTyped    r  n c t1 t2
                             -> cTyped (S r) n c t1 t2.
  intros. induction r. inversion H.
  compute.
*)

(* cTyped isn't inductive so we use shortcuts to ignore invalid typings *)
Theorem types_are_types : forall r n c m t,
                                 cTyped r n c t (cType m) ->
                                 exists l, t = cType (m + (S l)).
  destruct r. intros. intuition.
  simpl. repeat (dependent destruction t; intuition).
  exists (n0 - (S m)).
  assert (n0 = m + S (n0 - S m)).
  omega. rewrite <- H0. auto.
Qed.

(* Variables can have arbitrary types *)
Theorem var0_typed : forall n c ty,
                     exists r,
                            cTyped r (S n) (cons cT ty n c) ty (cVar 0).
  intros. exists 1. simpl. assert (0 < S n). apply (lt_0_Sn n).
  exists H. unfold betaEquiv. exists ty. exists 0. exists 0.
  simpl. auto.
Qed.

Lemma nth_append : forall A l m n (v1 : Vec A l)
                                  (v2 : Vec A m)
                                  (f1 : n < l)
                                  (f2 : n < l + m),
                          nth v1 (of_nat_lt f1)
                        = nth (append v1 v2) (of_nat_lt f2).
  intros. destruct v1. inversion f1.
  dependent induction n. auto. simpl. destruct v1. inversion f1.
  inversion H0.
  apply (IHn).
Qed.

(* Appending a suffix to our context doesn't prevent us typing terms *)
Theorem var_irrelevance : forall r n o c1 c2 ty m,
                                 cTyped r  n              c1     ty (cVar m)
                              -> cTyped r (n + o) (append c1 c2) ty (cVar m).
  intros. destruct r. auto.
  destruct n. simpl. destruct H. inversion x.
  simpl. destruct H. assert (m < S (n + o)). omega.
  exists H0.
  assert (p := nth_append cT (S n) o m c1 c2 x H0).
  rewrite p in H. auto.
Qed.
(*
Theorem context_irrelevance : forall r n o c1 c2 ty tm,
                                     cTyped r n c1 ty tm
                                  -> cTyped r (n + o) (append c1 c2) ty tm.
  intros. destruct r. auto. dependent destruction tm.
  repeat (unfold cTyped; intuition).
  apply (var_irrelevance (S r) n o c1 c2 ty n0 H).
  repeat (unfold cTyped; intuition).
  repeat (unfold cTyped; intuition).
  repeat (unfold cTyped; intuition).
  repeat (unfold cTyped; intuition).
  repeat (unfold cTyped; intuition).
  repeat (unfold cTyped; intuition).
  dependent destruction ty.
*)

(* Everything in 'Type x' is also in 'Type (x + y)' *)
(*
Theorem cumulative : forall x y t n c1 r1,
                     exists r2 c2,
                            (cTyped r1 n c1 (cType  x     ) t) ->
                            (cTyped r2 n c2 (cType (x + y)) t).
  intros. eapply ex_intro. eapply ex_intro. destruct r1. simpl. intuition.
  dependent inversion t.

  simpl. intro. instantiate (2 := 1). simpl.
  apply (lt_plus_trans n0 x y). auto.

  eapply ex_intro. simpl. intro. destruct H. exists x0.
  unfold betaEquiv. destruct H. destruct H. destruct H. exists (cType (x + y)).
  exists x2. exists x3. destruct H.
  assert (cSteps x2 (nth c1 (of_nat_lt x0)) = cSteps x3 (cType x)).
  rewrite H. rewrite H0. auto. intuition.
*)