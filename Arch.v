(* PowerPlay is a cognitive architecture, a design for a mind, which aims to be
 * unboundedly powerful whilst also being practical. Here, we'll produce a
 * specification for PowerPlay, which implementations can check for
 * conformance.
 *
 * We use the Coq proof assistant to formalise our specification.
 *)

Require Import Util.
Require Import List.
Require Import Program.

(* First we describe the domain that PowerPlay will be working in *)
Module Type DomainSig.

  (* Problem describes PowerPlay's inputs. These could be, for example,
   * theorems to prove or robot control decisions to make.
   *)
  Parameter Problem  : Type.

  (* Solution describes PowerPlay's (ideal) output. A Solution is parameterised
   * by the Problem we asked it to solve.
   *
   * Since Solutions are opaque to PowerPlay, implementations should ensure
   * they are'correct by construction'. In other words, having the type
   * 'Solution p' should be proof that a value solves p.
   *)
  Parameter Solution : Problem -> Type.
End DomainSig.

(* Next we derive a few definitions *)
Module Type PPSig (Domain : DomainSig).
  Import Domain.

  (* A Solver turns Problems into their Solutions. This is undecidable in
   * general, so we use 'option' to allow the possibility of failure.
   *)
  Definition Solver := forall p, option (Solution p).

  (* A State contains a Solver and a list of Problems it can provably solve.
   * This is a tuple of (solver, list, proof). The proof says that being in the
   * list implies that solver can find a Solution.
   *)
  Definition State
          := { sl : Solver * list Problem
             & let solver   := fst sl in
               let problems := snd sl in
                   forall p,
                          In p problems -> solver p <> None}.
  Definition stateSolver   (s : State) : Solver       := fst (projT1 s).
  Definition stateProblems (s : State) : list Problem := snd (projT1 s).

  (* We can always define the trivial State which can't solve anything *)
  Definition trivial : State.
    unfold State. refine (existT _ (fun x => None, nil) _).

    (* There are no Problems in an empty list, so 'In p problems' is False *)
    simpl. intuition.
  Qed.

  (* 'Improvement s' is a State containing the same Problems as s, plus an
   * extra one which the Solver in s cannot solve.
   *)
  Definition Improvement (s : State) :=
             {s' : State & exists p, (* p is the new problem *)
                                  stateProblems s' = p :: (stateProblems s)
                               /\ stateSolver s p = None}.
End PPSig.

(* Now we can describe the metaprogramming 'Searcher' *)
Module Type SearchSig (Domain : DomainSig) (PP : (PPSig Domain)).
  Import PP.

  (* The key to PowerPlay is a domain-specific Searcher which finds 'better'
   * Solvers, where 'better' is defined as provably-solving more Problems.
   *
   * Finding Improvements is undecidable so we use an 'option' wrapper again.
   *)
  Parameter Searcher : Type.

  (* PowerPlay must be parameterised by a Searcher, since building a Searcher
   * requires knowledge of the Problem and Solution types.
   *)
  Parameter searcher : Searcher.
End SearchSig.

(* The simplest form of Searcher just turns States into States *)
Module PPSearch (PP : PPSig) <: SearchSig.
  Definition Searcher := forall s, option (PP.Improvement s).
End PPSearch.

Module PPsearcher (PPUtil

End PPSig.

(* Now we can define our PowerPlay function, parameterised by a PPSig *)
Module PP (Sig : PPSig).
  Import Sig.

  (* Pull new States out of Improvements. We also return a proof that the new
   * State differs from our argument, in case anyone thinks we're cheating.
   *)
  Definition impState (s : State)
                      (i : Improvement s)
                         : {s' : State | s <> s'}.
    refine (existT _ (projT1 i) _). intuition. destruct i. destruct e.
    destruct a. simpl in H. destruct H. destruct s.
    unfold stateProblems in e. simpl in e. unfold stateSolver in e0.
    simpl in e0. simpl in e1. destruct x. simpl in e. simpl in e0.
    simpl in e1. assert (List.In x0 l). rewrite e. intuition.
    assert (p := e1 x0 H). rewrite e0 in p. inversion p. inversion H0.
  Defined.
  Arguments impState [s] i.

  (* We give PowerPlay a decreasing numeric argument as a 'timeout', to
   * ensure termination.
   *)
  Fixpoint PowerPlay' (s  : State)
                      (n  : nat)
                        : State
        := match n with
               | 0    => s (* Halt *)
               | S n' =>
           match searcher s with
               | None    => s (* No point recursing *)
               | Some s' => PowerPlay' (projT1 (impState s')) n'
           end
           end.
  Definition PowerPlay := PowerPlay' trivial.
End PP.

(* One problem with the above specification is that the Searcher can get
 * 'stuck'. Since it is trying to perform an undecidable task, and since it
 * must terminate at some point, there will always be cases where it returns
 * None. When this happens there's no point 'trying again' since it's a pure
 * function, so will just get 'stuck' again.
 * We can mitigate this by using the 'timeout' we give to the PowerPlay
 * function as an extra argument to our Searcher. This extra information allows
 * the Searcher to behave differently, eg. trying alternative branches, while
 * remaining referentially transparent.
 *)
Module Type PPN.
  (* Use the definitions as PP *)
  Parameter Problem : Type.
  Parameter Solution : Problem -> Type.
  Definition Solver := forall p, option (Solution p).
  Require Import List.
  Definition State
          := { sl : Solver * list Problem
             & let solver   := fst sl in
               let problems := snd sl in
                   forall p,
                          In p problems ->
                          exists s,
                                 solver p = Some s}.
  Definition stateSolver   (s : State) : Solver       := fst (projT1 s).
  Definition stateProblems (s : State) : list Problem := snd (projT1 s).
  Definition trivial : State.
    unfold State. exists (fun x => None, nil).
    simpl. intuition.
  Qed.
  Definition Improvement (s : State) :=
             {s' : State & exists p, (* p is the new problem *)
                                  stateProblems s' = p :: (stateProblems s)
                               /\ stateSolver s p = None}.

  Definition impState (s : State) (i : Improvement s) := projT1 i.
  Arguments impState [s] i.

  (* Our Searcher type is parameterised by a timeout *)
  Definition SearcherN := forall (n : nat) s, option (Improvement s).
  Parameter searcher : SearcherN.

  (* PowerPlay passes its timeout to the Searcher *)
  Fixpoint PowerPlayN' (s  : State)
                       (n  : nat)
                           : State
        := match n with
               | 0 => s (* Halt *)
               | S n' =>
           match searcher n' s with
               | None    => PowerPlayN'           s   n'
               | Some s' => PowerPlayN' (impState s') n'
           end
           end.
  Definition PowerPlayN := PowerPlayN' trivial.
End PPN.

(* An interesting special-case occurs when the Problems we're trying to solve
 * are how to make better Searchers. This can be used to make a self-improving
 * Searcher.
 *)
Module Type PPR.
  (* We use the same definitions as PP *)
  Parameter  Problem  :  Type.
  Parameter  Solution :  Problem -> Type.
  Definition Solver   := forall p, option (Solution p).

  Require Import List.
  Definition State
          := { sl : Solver * list Problem
             & let solver   := fst sl in
               let problems := snd sl in
                   forall p,
                          In p problems ->
                          exists s,
                                 solver p = Some s}.
  Definition stateSolver   (s : State) : Solver       := fst (projT1 s).
  Definition stateProblems (s : State) : list Problem := snd (projT1 s).

  Definition Improvement (s : State) :=
             {s' : State & exists p, (* p is the new problem *)
                                  stateProblems s' = p :: (stateProblems s)
                               /\ stateSolver s p = None}.

  Definition impState (s : State) (i : Improvement s) := projT1 i.
  Arguments impState [s] i.

  Definition Searcher := forall s, option (Improvement s).

  Parameter searcher : Searcher.

  (* By definition, Searchers can only improve Solvers. Hence any
   * self-improving implementation must have isomorphic Searchers and Solvers.
   *)
  Definition Recursive_Condition := Iso Searcher Solver.
  Parameter  recursive_condition :  Recursive_Condition.

  Lemma se_so : Searcher -> Solver.
    destruct recursive_condition. auto.
  Defined.

  Lemma so_se : Solver -> Searcher.
    destruct recursive_condition. auto.
  Defined.

  (* Not only should Searchers and Solvers be isomorphic, but their domains
   * (States and Problems) and codomains (Improvements and Solutions) need to
   * be isomorphic too. We could derive these isomorphisms from
   * recursive_condition, but since Improvements and Solutions are parameterised
   * by different types, that gets very messy. Instead, we leave it up to the
   * implementations, since they'll have concrete types to play with.
   *)
  Definition Prob_State := Iso Problem State.
  Parameter  prob_state :  Prob_State.

  Lemma probState : Problem -> State.
    destruct prob_state. auto.
  Defined.

  Lemma stateProb : State -> Problem.
    destruct prob_state. auto.
  Defined.

  Definition Sol_Imp (p : Problem) := Iso (Solution p)
                                          (Improvement (probState p)).
  Parameter  sol_imp  :  forall p, Sol_Imp p.

  Lemma solImp : forall p, Solution p -> Improvement (probState p).
    intro. destruct (sol_imp p). auto.
  Defined.

  Lemma impSol : forall p, Improvement (probState p) -> Solution p.
    intro. destruct (sol_imp p). auto.
  Defined.

  (* solState turns a 'Solution p' into an 'Improvement (probState p)' then
   * extracts the improved State. We also return a proof that we've not cheated
   * by returning 'probState p'.
   *)
  Require Import Program.
  Lemma solState : forall p, Solution p -> {s : State | s <> probState p}.
    intros. destruct (solImp p X). refine (existT _ x _). intuition.
    destruct H. destruct e. destruct H.
    induction (stateProblems x). dependent destruction H0.
    assert (a = x0). replace a with (hd x0 (a :: l)). rewrite H. auto. auto.
    destruct H1. destruct IHl.
    replace (l = a :: l) with (tl (a :: l) = tl (a :: a :: l)).
    rewrite <- H. auto. f_equal.
  Defined.
  Arguments solState [p] _.

  (* Now we can specify a PowerPlay system which can improve other PowerPlay
   * systems with the same Problem, State, etc. implementations.
   *)
  Fixpoint recPP  (s : State)
                  (n : nat)
                     : State
        := let problem  := stateProb s in
           let searcher := fst (projT1 s) in
           match n with
               | 0    => s (* Halt *)
               | S n' =>
           match searcher problem with
               | None    => s (* No point recursing *)
               | Some s' => recPP (projT1 (solState s')) n'
           end
           end.
End PPR.

(* We can 'tie the knot' and get a PPR implementation to improve itself *)
Module SelfImproving (M : PPR).
  Import M.

  (* We represent self-improving sequences as Streams (infinite lists). *)

  (* We can make a Stream of improving States by iterating calls to recPP.
   * We double the timeout on each call to recPP, so that the State doesn't get
   * 'stuck' prematurely.
   *)
Require Import NZPow. Import NZPowProp
Definition p := pow 2 4.
  CoInductive ImprovingStates : nat -> State -> Type :=
    | stCons : forall n s,
                      ImprovingStates n s -> ImprovingStates (S n) (recPP s n).

  Definition improveFrom (start : State) := stCons 0 start.
End SelfImproving.

  (* Again, we can pass our 'timeout' to the Searcher to avoid getting
   * 'stuck'. We need to keep track of it in our State too, since it is
   * needed in our proofs.
   *)
Definition SolverN := forall (n : nat), Solver.

Definition StateN := { sln : (SolverN * list Problem) * nat
                     & let solver    := fst (fst sln) in
                       let problems := snd (fst sln) in
                       let n        := snd sln       in
                       forall p, In p problems ->
                       exists s, solver n p = Some s}.

Definition solverN   (s : StateN) := fst (fst (projT1 s)).
Definition problemsN (s : StateN) := snd (fst (projT1 s)).
Definition timeoutN  (s : StateN) := snd      (projT1 s).

Definition ImprovementN (s : StateN)
        := { s' : StateN
           & exists p,
                    (* p is a previousy-unsolvable problem *)
                    problemsN s' = p :: (problemsN s)
                    /\ solverN s (timeoutN s) p = None}.

Definition PImprovementN (p1 : Problem = StateN)
                         (p2 : Problem)
                             : Type
        := ImprovementN (cast p1 p2).

Definition solStateN : forall p
                       (s : Solution = PImprovementN p)
                       q,
                       Solution q                  ->
                       StateN.
  intros. assert (PImprovementN p q).
  rewrite <- s. exact X. 
  destruct X0. exact x.
Qed.
Arguments solStateN [p s q] _.

Fixpoint recPPN (p : Problem = StateN)
                (q : Solution = PImprovementN p)
                (s : StateN)
                (n : nat)
                   : StateN
      := let problem  := cast (eq_sym p) s in
         let searcher := solverN  s        in
         let timeout  := timeoutN s        in
         match n with
             | 0    => s (* Halt *)
             | S n' =>
         match searcher timeout problem with
             | None    => recPPN p q s n'
             | Some s' => let st' := solStateN (*p q problem*) s' in
                              recPPN p q st' n'
         end
         end.

(* Now we verify some properties of PowerPlay *)

(* If an Improvement can be found, PowerPlay will find it in 1 step *)
Theorem PPimproves1 :
        forall s se i,
               se s = Some i
            -> PowerPlay' s se 1 = projT1 i.
  intros. simpl. rewrite H. auto.
Qed.

Theorem PPimprovesS :
        forall s se i n,
               se s = Some i
            -> PowerPlay' s se (S n) = PowerPlay' (projT1 i) se n.
  intros. simpl. rewrite H. auto.
Qed.

Theorem PPNimproves1 :
        forall s se i,
               se 0 s = Some i
            -> PowerPlayN' s se 1 = projT1 i.
  intros. simpl. rewrite H. auto.
Qed.

Theorem PPNimprovesS :
        forall s se i n,
               se n s = Some i
            -> PowerPlayN' s se (S n) = PowerPlayN' (projT1 i) se n.
  intros. simpl. rewrite H. auto.
Qed.

Theorem recPPimproves1 :
        forall s p q i,
               solver s (cast (eq_sym p) s) = Some i
            -> recPP p q s 1 = solState q i.
  intros. simpl. replace (fst (projT1 s)) with (solver s).
  destruct (solver s (cast (eq_sym p) s)). replace s0 with i.
  auto. inversion H. auto. inversion H. auto.
Qed.

Theorem recPPimprovesS :
        forall s p q i n,
               solver s (cast (eq_sym p) s) = Some i
            -> recPP p q s (S n) = recPP p q (solState q i) n.
  intros. simpl. replace (fst (projT1 s)) with (solver s).
  destruct (solver s (cast (eq_sym p) s)). inversion H. auto.
  inversion H. auto.
Qed.

Theorem recPPNimproves1 :
        forall s p q i,
               solverN s (timeoutN s) (cast (eq_sym p) s) = Some i
            -> recPPN p q s 1 = solStateN p q (cast (eq_sym p) s) i.
  intros. simpl.
  destruct ((solverN s) (timeoutN s) (cast (eq_sym p) s)).
  inversion H. auto. inversion H.
Qed.

(* Problems are never removed from the list *)
