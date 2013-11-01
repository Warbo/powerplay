(* Quick and simple "spike" specification of PowerPlay *)

(* Contains exponential function*)
Require Import NPeano.

(* Problems and Solutions are parameters *)
Parameter Problem  : Type.
Parameter Solution : Problem -> Type.

(* Solvers might solve Problems within a timeout *)
Definition Solver := forall p, nat -> option (Solution p).

(* If a Solver does not return None, it can solve a Problem *)
Definition Solves (s : Solver) p n: Prop
        := s p n <> None.

(* We can define a trivial Solver and prove it can't solve anything *)
Definition trivial_solver : Solver
        := fun _ _ => None.

Theorem trivial : forall p n, ~(Solves trivial_solver p n).
  intuition.
Qed.

(* One Solver Dominates another if it Solves all the same Problems and more *)
Definition Dominates (s1 s2 : Solver) : Prop
        := (forall p n, Solves s2 p n -> Solves s1 p n) /\
          ~(forall p n, Solves s1 p n -> Solves s2 p n).

(* Searchers might find a Solver which Dominates another within a timeout *)
Definition Searcher := forall s1 (n : nat),
                              option {s2 | Dominates s2 s1}.

(* We take a Searcher an a parameter *)
Parameter searcher : Searcher.

(* We can relax the Dominates condition to only prevent regressions *)
Definition NoWorse s1 s2 : Prop
        := Dominates s1 s2 \/ s1 = s2.

(* By returning our input Solver instead of None, a Searcher becomes NoWorse *)
Definition searcher' s1 (n : nat) : {s2 | NoWorse s2 s1}.
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
CoInductive NoWorseStream s1 : Type :=
  nwsCons : forall s2,
                   NoWorse s2 s1    ->
                   NoWorseStream s2 ->
                   NoWorseStream s1.

(* PowerPlay makes a NoWorseStream by searching with increasing timeouts *)
CoFixpoint powerplay' s n : NoWorseStream s
        := let found := searcher' s (2 ^ n) in
           let s'    := projT1 found  in
           let proof := projT2 found  in
               nwsCons  s
                        s'
                        proof
                       (powerplay' s' (S n)).

(* Set initial values *)
Definition powerplay : NoWorseStream trivial_solver
        := powerplay' trivial_solver 0.