(* Use lambda calculus as a generic problem solver *)
Require Import Simple.

(* We will index our environment using *)
Require Import Fin.

(* Rename Fin.t *)

(* Our lambda expressions *)
Inductive Expr : nat -> Type :=
  | Lam : forall n, Expr (S n) -> Expr n
  | App : forall n m, Expr n -> Expr m -> Expr (max n m)
  | Var : forall n, 