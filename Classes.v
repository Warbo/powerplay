(* PowerPlay is a problem-solving algorithm which aims to be unboundedly
 * powerful whilst also being practical. Here, we'll produce a specification for
 * PowerPlay, which implementations can check for conformance.
 *
 * We use the Coq proof assistant to formalise our specification, using type
 * classes to keep our implementation polymorphic.
 *)

Require Import Util.
Require Import List.
Require Import Program.
Require Import Peano_dec.

(* First we abstract over the Domain that PowerPlay will be working in.
 * Problems are the things we want to solve, for example theorems to prove or
 * robot control decisions to make, Solutions solve Problems.
 *
 * The type of each Solution is parameterised by the particular Problem it
 * solves.
 *)
Inductive Domain : Type :=
  mkDomain : forall (p : Type) (s : p -> Type), Domain.
Definition Problem (d : Domain) : Type
        := match d with mkDomain p s => p end.
Definition Solution (d : Domain) : Problem d -> Type
        := match d with mkDomain p s => s end.

(* Solvers turn Problems into Solutions.
 *
 * We use an 'option' type to allow the possibility of failure. We also give
 * Solvers a numeric argument, in case they want a 'timeout'. They're free to
 * ignore it otherwise.
 *)
Definition Solver' (D : Domain) := forall p, nat -> option (Solution D p).

(* Solver is a monotonic restriction of Solver': increasing the timeout of a
 * Solver will not turn a solvable Problem into an unsolvable one. The
 * particular Solution that's found is allowed to differ.
 *)
Definition Solver (D : Domain) := {s : Solver' D |
                                   forall p n,
                                          s p n <> None -> s p (S n) <> None}.

(* This throws away the monotonic proof *)
Definition solver (D : Domain) (s : Solver D) : Solver' D := projT1 s.

(* Next we abstract over the method of proving improvement.
 *
 * The key to PowerPlay is the abilty to prove that one Solver Dominates
 * (provably-solves more Problems than) another. Different variants will do
 * this in different ways, so we abstract over the specifics.
 *
 * 'SolvableBy s' is an abstract container for Problems which are provably-
 * solvable by Solver s. 'In' represents membership and 'Dominates' is a kind
 * strict-subset relationship, with the added property that the superset must
 * contain a Problem unsolvable by the subset's Solver.
 *)
Inductive Dominate : Type := mkDominate
        : forall (D : Domain)

                 (solvable_by : Solver D -> nat -> Type)

                 (is_in : forall {s n}
                                 (_ : Problem D)
                                 (_ : solvable_by s n),
                                 Prop)

                 (dominates : forall {s1 s2 n}
                                     (_ : solvable_by s1 n)
                                     (_ : solvable_by s2 n),
                                     Prop)

                 (* Axioms *)
                 (solvable : forall {s n} {sb : solvable_by s n} p
                             (_ : is_in p sb),
                             (solver D s) p n <> None)

                 (dom_super : forall {s1} {s2} {n} {p}
                                     {sb1 : solvable_by s1 n}
                                     {sb2 : solvable_by s2 n}
                                     (_ : dominates sb1 sb2)
                                     (_ : is_in p sb2),
                                     is_in p sb1)

                 (dom_improves : forall {s1 s2 n}
                                        (sb1 : solvable_by s1 n)
                                        (sb2 : solvable_by s2 n)
                                        (dom : dominates sb1 sb2),
                                 exists p,
                                        is_in p sb1               /\
                                        (solver D s1) p n <> None /\
                                        (solver D s2) p n =  None),

                    Dominate.

(* Projections *)
Definition DomDom (D : Dominate)
        :  Domain
        := match D with mkDominate d _ _ _ _ _ _ => d end.
Definition SolvableBy (D : Dominate)
        :  Solver (DomDom D) -> nat -> Type
        := match D with mkDominate _ s _ _ _ _ _ => s end.
Definition In (D : Dominate)
        :  forall {s n}, Problem (DomDom D) -> SolvableBy D s n -> Prop
        := match D with mkDominate _ _ i _ _ _ _ => i end.
Definition Dominates (D : Dominate)
        :  forall {s1 s2 n}, SolvableBy D s1 n -> SolvableBy D s2 n -> Prop
        := match D with mkDominate _ _ _ d _ _ _ => d end.

(* Now we describe PowerPlay's internal State, which contains a Solver and some
 * Problems it can provably-solve within some timeout.
 *)
Definition State (D : Dominate)
        := {sn : Solver (DomDom D) * nat & SolvableBy D (fst sn) (snd sn)}.

(* Useful projections *)
Definition stateSolver (D : Dominate)
                       (s : State D)
                          : Solver (DomDom D)
        := fst (projT1 s).

Definition stateTimeout (D : Dominate)
                        (s : State D)
                           : nat
        := snd (projT1 s).

Definition stateProblems (D : Dominate) (s : State D)
        :  SolvableBy D (stateSolver D s) (stateTimeout D s)
        := projT2 s.

(* Lifting Dominates from SolvableBy to State requires equal timeouts *)
Definition equal_timeouts (D     : Dominate)
                          (s1 s2 : State D)
                                 :  Prop
        := stateTimeout D s1 = stateTimeout D s2.

Lemma cast_timeouts (D : Dominate)
    : forall s1 s2 (p : equal_timeouts D s1 s2),
             (SolvableBy D (stateSolver  D s1)
                           (stateTimeout D s1) *
              SolvableBy D (stateSolver  D s2)
                           (stateTimeout D s1)).
  intros. unfold equal_timeouts in p.
  refine (stateProblems D s1, _). rewrite p.
  exact  (stateProblems D s2).
Defined.

Definition dominates (D : Dominate)
                     (s1 s2 : State D)
                            : Prop
        := exists p, let pair := cast_timeouts D s1 s2 p
                      in Dominates D (fst pair) (snd pair).

(* 'Improvement s' is a State who's Solver Dominates that of s. *)
Definition Improvement (D : Dominate)
                       (s  : State D)
        := {s' : State D | dominates D s' s}.

(* In order to improve, PowerPlay needs a domain-specific Searcher to find a
 * Solver which Dominates the current one.
 *
 * Finding Improvements is undecidable so we use an 'option' wrapper and a
 * timeout again.
 *)
Definition Searcher' (D : Dominate)
        := forall s, nat -> option (Improvement D s).

(* Again, our proofs will be easier if Searchers are monotonic (increasing
 * the timeout never loses an Improvement).
 *)
Definition Searcher (D : Dominate)
        := {s : Searcher' D |
            forall st n,
                   s st n <> None -> s st (S n) <> None}.
Definition searcher (D : Dominate)
                    (s : Searcher  D)
                       : Searcher' D
        := projT1 s.

(* We require some initial conditions in order to improve. Specifically,
 * PowerPlay requires a Searcher and an initial State; if SolvableBy wasn't
 * abstract we could define initial values trivially ('fun _ _ => None' is a
 * valid Searcher and a valid Solver) but improvements would never be found.
 *)
Inductive InitialConditions : Type := mkIC
        : forall (D : Dominate)
                 (initial_searcher : Searcher D)
                 (initial_state    : State    D),
                 InitialConditions.

(* Projections *)
Definition InitialDom (I : InitialConditions)
        :  Dominate
        := match I with mkIC d _ _ => d end.
Definition InitialSearcher (I : InitialConditions)
        :  Searcher (InitialDom I)
        := match I with mkIC _ s _ => s end.
Definition InitialState (I : InitialConditions)
        :  State (InitialDom I)
        := match I with mkIC _ _ s => s end.

(* Now we can describe PowerPlay's main-loop, which turns one State into
 * another.
 *)
Definition PPStep (I : InitialConditions) : Type
        := State (InitialDom I) -> State (InitialDom I).

(* We can define a simple PowerPlay implementation by iterating the initial
 * Searcher to produce better and better States.
 *)
Definition simple_pp_step (I : InitialConditions)
                             : PPStep I
        := let D             := InitialDom I in
           let init_searcher := searcher D (InitialSearcher I) in
               (fun s => match init_searcher s (stateTimeout D s) with
                             | None    => s           (* No Improvement *)
                             | Some s' => (projT1 s') (*    Improvement *)
                         end).

CoInductive powerplay I (P : PPStep I) : Type :=
  cons : forall (s : State (InitialDom I))
                (_ : powerplay I P),
                powerplay I P.

CoFixpoint simple_pp' (I : InitialConditions)
                      (s : State (InitialDom I))
        := cons I (simple_pp_step I) s (simple_pp' I (simple_pp_step I s)).

(* The PowerPlay instance above is pretty dumb; it's basically a technique for
 * augmenting an existing heuristic 'stateSolver initial_state', with a fixed,
 * existing meta-heuristic 'initial_searcher'.
 *
 * We get the benefit of having verified plumbing and the existence of the
 * Searcher allows us to get away with a poor Solver, but we still have to write
 * the Searcher itself, which is a much more difficult task than the plumbing.
 *
 * However, now that we've got PowerPlay at our disposal, we can use it write
 * our Searcher for us! We will now write a modified PowerPlay instance which
 * can improve its own Searcher, to create a truly self-improving system which
 * we can bootstrap with a poor Searcher.
 *)

(* We make State a subset of Problem and Improvement a subset of Solution so
 * that we can turn Searchers into Solvers and hence make them available for
 * improvement.
 *)
Inductive RecDom D1 : Type := mkRD
       :  forall D2
                 (pp : Problem (DomDom D1) ->
                       Problem (DomDom D2))
                 (ps : State D2 ->
                       Problem (DomDom D2))
                 (si : forall s,
                              Improvement D2 s ->
                              Solution (DomDom D2) (ps s)),
                 RecDom D1.

(* Projection functions *)
Definition NonRDom {D} (RD : RecDom D)
        :  Dominate
        := D.
Definition RDom {D} (RD : RecDom D)
        :  Dominate
        := match RD with mkRD D2 _ _ _ => D2 end.
Definition RDomDom {D} (RD : RecDom D)
        :  Domain
        := DomDom (RDom RD).

(* By augmenting our Dominate, Searchers become a subset of Solvers *)
Theorem search_solv_subset {D} (RD : RecDom D)
                           (s  : Solver (RDomDom RD))
                               : Searcher (RDom RD).
  destruct RD. assert (Searcher' D2).
  unfold Searcher'. destruct s. unfold Solver' in x.
  intros. assert (q := x (ps s) H).
  apply (si srefine (existT _ _). ( ds). intro. intros. destruct ds.
  assert Problem. refine (inr s0).
  exact (inr s). assert (p := n (prob_sum s)). (sum_coalesce X (fun _ => None)). unfold Solver. intro. destruct X.
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
