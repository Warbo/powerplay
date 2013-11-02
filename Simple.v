(* Quick and simple "spike" specification of PowerPlay *)

(* Bring in an exponential function *)
Require Import NPeano.

(* Problems and Solutions are parameters, so we put them in a Class *)
Class Domain := {
  Problem  : Type;
  Solution : Problem -> Type
}.

(* Solvers might solve Problems within a timeout *)
Definition Solver {D : Domain} := forall p,
                                         nat ->
                                         option (Solution p).

(* If a Solver does not return None, it can solve a Problem *)
Definition Solves {D : Domain} (s : Solver) p n: Prop
        := s p n <> None.

(* We can define a trivial Solver and prove it can't solve anything *)
Definition trivial_solver {D : Domain} : Solver
        := fun _ _ => None.

(* One Solver Dominates another if it Solves all the same Problems and more *)
Definition Dominates {D : Domain} (s1 s2 : Solver) : Prop
        := (forall p n, Solves s2 p n -> Solves s1 p n) /\
          ~(forall p n, Solves s1 p n -> Solves s2 p n).

(* Searchers might find a Solver which Dominates another within a timeout *)
Definition Searcher {D : Domain} := forall s1 (n : nat),
                                           option {s2 | Dominates s2 s1}.

(* Our Searcher is a parameter, so we wrap it in a Class *)
Class GivenSearcher {D : Domain} := {
  searcher : Searcher
}.

(* We can relax the Dominates condition to only prevent regressions *)
Definition NoWorse {D : Domain} s1 s2 : Prop
        := Dominates s1 s2 \/ s1 = s2.

(* By returning our input Solver instead of None, a Searcher becomes NoWorse *)
Definition searcher' {D : Domain} {G : GivenSearcher}
                     s1 (n : nat) : {s2 | NoWorse s2 s1}.
  (* Propose a value for s2 *)
  refine (existT _
                 (match searcher s1 n with
                      | None    => s1
                      | Some s' => projT1 s'
                  end)
                 _).

  (* Prove by case-analysis on 'searcher s1 n' that s2 is NoWorse *)
  destruct (searcher s1 n).

  (* searcher s1 n = Some s. Solve by extracting the proof from s *)
  exact (or_introl (projT2 s)).

  (* searcher s1 n = None. Solve trivially *)
  exact (or_intror eq_refl).
Defined.

(* Define an infinite stream of Solvers, each NoWorse than the last *)
CoInductive NoWorseStream {D : Domain} s1 : Type :=
  nwsCons : forall s2,
                   NoWorse s2 s1    ->
                   NoWorseStream s2 ->
                   NoWorseStream s1.

(* Projection function to extract a Solver from a NoWorseStream *)
Fixpoint get_solver {D : Domain} {s1} (n : nat)
                    (nws : NoWorseStream s1) : Solver :=
  match n with
      | 0 => s1
      | S n' => match nws with
                    | nwsCons _ _ nws' => get_solver n' nws'
                end
  end.

(* PowerPlay makes a NoWorseStream by searching with increasing timeouts *)
CoFixpoint powerplay' {D : Domain} {G : GivenSearcher}
                      s n : NoWorseStream s
        := let found := searcher' s (2 ^ n) in
           let s'    := projT1 found  in
           let proof := projT2 found  in
               nwsCons  s
                        s'
                        proof
                       (powerplay' s' (S n)).

(* Set initial values *)
Definition powerplay {D : Domain} {G : GivenSearcher}
        :  NoWorseStream trivial_solver
        := powerplay' trivial_solver 0.
