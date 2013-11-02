(* A straightforward, non-recursive PowerPlay implementation *)

(* We'll implement the specification in Simple to find prime factors *)
Require Import Simple.

(* First we define what it means to be Prime *)
Definition Prime n := forall x y,
                             x * y = n -> x = 1 \/ y = 1.

(* Next we define prime factor lists (PFLists) *)
Inductive PFList n : Type :=
  (* If n is Prime, its PFList is a singleton of itself *)
  | sNil  : Prime n -> PFList n

  (* Otherwise, a PFList can be made from PFLists of two factors *)
  | sCons : forall x y,
                   x * y = n  ->
                   PFList x   ->
                   PFList y   ->
                   PFList n.

(* Now our Domain is turning Naturals into their PFLists *)
Instance Factoring : Domain := {
  Problem  := nat;
  Solution := PFList
}.

(* Now we get to the interesting part: the Searcher *)
Instance Trivial : GivenSearcher := {
  searcher := fun _ _ => None
}.

Definition s := (get_solver 10 powerplay).
Theorem foo : s = trivial_solver.
unfold s. simpl.