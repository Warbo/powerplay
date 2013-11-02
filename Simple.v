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

(* One Solver Dominates another if it Solves all the same Problems and more *)
Definition Dominates {D : Domain} (s1 s2 : Solver) : Prop
        := (forall p n, Solves s2 p n -> Solves s1 p n) /\
          ~(forall p n, Solves s1 p n -> Solves s2 p n).

(* Solvers are opaque, but we need a transparent representation *)
Class Lang {D : Domain} : Type := {
  AST       : Type;
  interpret : AST -> Solver
}.

(* Searchers look for a Solver AST which Dominates another *)
Definition Searcher {D : Domain} {L : Lang}
        := forall ast1 (n : nat),
                  option {ast2 | Dominates (interpret ast2)
                                           (interpret ast1)}.

(* Our Searcher is a parameter, so we wrap it in a Class *)
Class GivenSearcher {D : Domain} {L : Lang} := {
  searcher : Searcher
}.

(* We can relax the Dominates condition to only prevent regressions *)
Definition NoWorse {D : Domain} s1 s2 : Prop
        := Dominates s1 s2 \/ s1 = s2.

(* By returning our input Solver instead of None, a Searcher becomes NoWorse *)
Definition searcher' {D : Domain} {L : Lang} {G : GivenSearcher}
                     ast1 (n : nat)
        :  {ast2 | NoWorse (interpret ast2)
                           (interpret ast1)}.
  (* Propose a value for ast2 *)
  refine (existT _
                 (match searcher ast1 n with
                      | None    => ast1
                      | Some s' => projT1 s'
                  end)
                 _).

  (* Prove by case-analysis on 'searcher ast1 n' that ast2 is NoWorse *)
  destruct (searcher ast1 n).

  (* searcher ast1 n = Some s. Solve by extracting the proof from s *)
  exact (or_introl (projT2 s)).

  (* searcher ast1 n = None. Solve trivially *)
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
CoFixpoint powerplay' {D : Domain} {L :Lang} {G : GivenSearcher}
                      ast n : NoWorseStream (interpret ast)
        := let found := searcher' ast (2 ^ n) in
           let ast'  := projT1 found  in
           let proof := projT2 found  in
               nwsCons  (interpret ast)
                        (interpret ast')
                        proof
                       (powerplay' ast' (S n)).

(* Set initial values *)
Definition powerplay {D : Domain} {L : Lang} {G : GivenSearcher}
                      ast
        :  NoWorseStream (interpret ast)
        := powerplay' ast 0.
