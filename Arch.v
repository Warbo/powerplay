(* PowerPlay is a problem-solving algorithm which aims to be unboundedly
 * powerful whilst also being practical. Here, we'll produce a specification for
 * PowerPlay, which implementations can check for conformance.
 *
 * We use the Coq proof assistant to formalise our specification.
 *)

Require Import Util.
Require Import List.
Require Import Program.
Require Import Peano_dec.

(* First we abstract over the domain that PowerPlay will be working in *)
Module Type DomainSpec.

  (* Problems are the things we want to solve, for example theorems to prove or
   * robot control decisions to make.
   *)
  Parameter Problem  : Type.

  (* Solutions solve problems. The type of each Solution is parameterised by the
   * particular Problem it solves.
   *
   * Since Solutions are opaque to PowerPlay, implementations should ensure
   * they are 'correct by construction'. In other words, having the type
   * 'Solution p' should be proof that a value solves p; no checking required.
   *)
  Parameter Solution : Problem -> Type.
End DomainSpec.

Module SolverF (Domain : DomainSpec).
  Import Domain.

  (* Solvers turn Problems into Solutions.
   *
   * We use an 'option' type to allow the possibility of failure. We also give
   * Solvers a numeric argument, in case they want a 'timeout', which they're
   * free to ignore.
   *)
  Definition Solver' := forall p, nat -> option (Solution p).

  (* All of our Solvers will be monotonic. Increasing their timeout will not
   * change a solvable Problem into an unsolvable one (although the particular
   * Solution is allowed to differ).
   *)
  Definition Solver := {s : Solver' |
                        forall p n,
                               s p n <> None -> s p (S n) <> None}.
  Definition solver (s : Solver) : Solver' := projT1 s.
End SolverF.

(* Next we abstract over the method of proving self-improvement. *)
Module Type DominatesSpec (Domain : DomainSpec).
  Import Domain.

  (* Instantiate a SolverF for this Domain *)
  Module SolverImp := SolverF Domain.
  Import SolverImp.

  (* The key to PowerPlay is the abilty to prove that one Solver Dominates
   * (provably-solves more Problems than) another. Different variants will do
   * this in different ways, so we abstract over the specifics.
   *
   * 'SolvableBy s' contains Problems provably-solvable by Solver s.
   *)
  Parameter SolvableBy : Solver -> nat -> Type.
  Axiom     In : forall s n, Problem -> SolvableBy s n -> Prop.
  Arguments In [s n] _ _.
  Axiom     solvable : forall s n p (sb : SolvableBy s n),
                       In p sb -> (solver s) p n <> None.
  Arguments solvable [s n] p sb _ _.

  (* Dominates is a strict superset relationship *)
  Axiom Dominates : forall s1 s2 n,
                           SolvableBy s1 n -> SolvableBy s2 n -> Prop.
  Arguments Dominates [s1 s2 n] _ _.

  Axiom dom_super : forall s1 s2 n p
                           (sb1 : SolvableBy s1 n)
                           (sb2 : SolvableBy s2 n),
                           Dominates sb1 sb2 -> In p sb2 -> In p sb1.

  (* Crucially, if s1 dominates s2, then s1 can solve a Problem s2 can't *)
  Axiom dom_improve : forall s1 s2 n
                             (sb1 : SolvableBy s1 n)
                             (sb2 : SolvableBy s2 n),
                             Dominates sb1 sb2 ->
                             exists p,
                             In p sb1       /\
                             (solver s1) p n <> None /\
                             (solver s2) p n =  None.
End DominatesSpec.

(* Now we describe PowerPlay's internal State *)
Module Type StateSpec (Domain : DomainSpec) (Dominates : DominatesSpec).
  Module Dominate := Dominates Domain.
  Export Dominate.
  Module SolverImp := SolverF Domain.
  Export SolverImp.

  Parameter State     : Type.
  Axiom stateSolver   : State -> Solver.
  Axiom stateTimeout  : State -> nat.
  Axiom stateProblems : forall s, SolvableBy (stateSolver  s)
                                             (stateTimeout s).

  Parameter Improvement : Type.
  Parameter Searcher    : Type.
End StateSpec.

Module StateF (Domain : DomainSpec) (Dominates : DominatesSpec) <: StateSpec.
  Module Dominate := Dominates Domain.
  Module SolverImp := SolverF Domain.
  Export Dominate.
  Export SolverImp.

  (* PowerPlay's current State contains a Solver and some Problems it can
   * provably-solve with some timout.
   *)
  Definition State := {sn : Solver * nat & SolvableBy (fst sn) (snd sn)}.

  (* Useful projections *)
  Definition stateSolver   (s : State) : Solver
          := fst (projT1 s).

  Definition stateTimeout  (s : State) : nat
          := snd (projT1 s).

  Definition stateProblems (s : State) : SolvableBy (stateSolver  s)
                                                    (stateTimeout s)
          := projT2 s.

  (* To prove one State Dominates another, we must identify their timeouts *)
  Definition equal_timeouts (s1 s2 : State) : Prop
          := stateTimeout s1 = stateTimeout s2.

  Lemma cast_timeouts : forall s1 s2,
                               equal_timeouts s1 s2
                            -> (SolvableBy (stateSolver  s1)
                                           (stateTimeout s1)
                             *  SolvableBy (stateSolver  s2)
                                           (stateTimeout s1)).
    intros. unfold equal_timeouts in H.
    refine (stateProblems s1, _). rewrite H. exact (stateProblems s2).
  Defined.

  Definition dominates (s1 s2 : State) : Prop
          := exists p, let pair := cast_timeouts s1 s2 p
                        in Dominates (fst pair) (snd pair).

  (* 'Improvement s' is a State who's Solver Dominates that of s. *)
  Definition Improvement (s  : State) := {s' : State | dominates s' s}.

  (* In order to improve, PowerPlay needs a domain-specific Searcher to find a
   * Solver which Dominates the current one.
   *
   * Finding Improvements is undecidable so we use an 'option' wrapper and a
   * timeout again.
   *)
  Definition Searcher' := forall s, nat -> option (Improvement s).

  (* Again, our proofs will be easier if Searchers are monotonic (increasing
   * the timeout never loses an Improvement).
   *)
  Definition Searcher := {s : Searcher' |
                          forall st n,
                                 s st n <> None -> s st (S n) <> None}.
  Definition searcher (s : Searcher) : Searcher' := projT1 s.
End StateF.

(* We require some initial conditions in order to improve *)
Module Type InitialConditions (Domain   : DomainSpec)
                              (Dominate : DominatesSpec).
  Module States := StateSpec Domain Dominate.
  Import States.

  (* PowerPlay requires a Searcher and an initial State; if SolvableBy wasn't
   * abstract we could define initial values trivially ('fun _ _ => None' is a
   * valid Searcher and a valid Solver) but improvements would never be found.
   *
   * Hence we take these as parameters.
   *)
  Parameter initial_searcher : Searcher.
  Parameter initial_state    : State.
End InitialConditions.

(* Now we can define the PowerPlay function *)
Module PPSpec (Domain   : DomainSpec)
              (Dominate : DominatesSpec)
              (Init     : InitialConditions).
  Module StateImp := StateSpec Domain Dominate.
  Module InitImp := Init Domain Dominate.
  Import StateImp.
  Import InitImp.

  (* We give PowerPlay a decreasing numeric argument as a 'timeout', to ensure
   * termination. We store its initial value in our State and pass this to our
   * Solvers, to ensure our States are comparable, and to our Searcher, to
   * avoid overly-restricting it.
   *)
  Fixpoint PowerPlay' (s  : State)
                      (n  : nat)
                          : State
        := match n with
               | 0    => s (* Halt *)
               | S n' =>
           match (searcher initial_searcher) s (stateTimeout s) with
               | None    => s (* No point recursing *)
               | Some s' => PowerPlay' (projT1 s') n'
           end
           end.
  Definition PowerPlay := PowerPlay' initial_state.
End PPSpec.

(* The PowerPlay specification above is pretty dumb; it's basically a technique
 * for augmenting an existing heuristic 'stateSolver initial_state', with a
 * fixed, existing meta-heuristic 'initial_searcher'.
 * We get the benefit of having verified plumbing, having the Searcher lets us
 * get away with a poor Solver, but we still have to write the Searcher itself,
 * which is a much more difficult task than the plumbing.
 *
 * However, now that we've got PowerPlay at our disposal, we can use it write
 * our Searcher for us! We will now write a modified PowerPlay specification
 * which can improve its own Searcher, to create a truly self-improving system
 * which we can bootstrap with a poor Searcher.
 *)

(* For PowerPlay to improve its Searcher, we must augment its Types *)
Module PlusSelf (Domain : DomainSpec) (Dominate : DominatesSpec) <: DomainSpec.
  Module States := StateSpec Domain Dominate.
  Import States.

  (* PowerPlay improves Solvers, which turn Problems into Solutions. We want it
   * to improve Searchers, which turn States into Improvements. Hence we must
   * unify States with Problems and Improvements with Solutions 
   *)

  (* We add State to Problem using a sum type. *)
  Definition Problem := sum Domain.Problem State.

  (* The sum_coalesce function will use Domain.Solution to turn Domain.Problem
   * values into Types and Improvement to turn State values into Types.
   *)
  Definition Solution := sum_coalesce Domain.Solution
                                      Improvement.

  (* We also provide theorems to tell other modules what we've done *)
  Definition prob_sum : State -> Problem := inr.
End PlusSelf.

(* Now we can define our recursive PowerPlay implementation *)
Module PPRecSpec (Domain : DomainSpec)
                 (Dominate : DominatesSpec)
                 (Init : InitialConditions).
  (* Use an augmented Domain *)
  Module DomainPlusSelf := PlusSelf Domain Dominate.
  Module InitImp := Init DomainPlusSelf Dominate.
  Import InitImp.

  (* Our augmented domain means that Searchers are a subset of Solvers *)
  Theorem search_solv_subset : Solver -> Searcher.
    intro. assert Searcher'. intro. destruct X.
    assert (p := n (prob_sum s)). (sum_coalesce X (fun _ => None)). unfold Solver. intro. destruct X.
    assert Searcher'. unfold Searcher'. 
          
  Theorem search_solve_iso : exists (f : Searcher -> Solver)
                                    (g : Solver   -> Searcher),
                                    inhabited (forall s, f (g s) = s) /\
                                    inhabited (forall s, g (f s) = s).
    assert (Searcher -> Solver).
    unfold Searcher. unfold Solver. intro. destruct X.
    unfold Solver'. unfold Problem.
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
