Require Import Syntax.
Require Import Containers.Generate.
Require Import GenerateUOT.
Require Import Notations.

Inductive test_sort := point | dist.
Generate OrderedType test_sort.

Inductive test_pred := dist_pp.
Definition test_pred_ar (p : test_pred) : list test_sort :=
  match p with
    | dist_pp => point::point::dist::nil
  end.

Instance test_sig : Signature := {
  sort := test_sort;
  pred := test_pred;
  pred_ar := test_pred_ar
}.

Inductive test_var :=
  | p : nat -> test_var
  | d : nat -> test_var.
Generate OrderedType test_var.

Definition test_sortof (v : test_var) :=
  match v with
    | p _ => point
    | d _ => dist
  end.

Instance test_env : Environment test_sig := {
  variable := test_var;
  sortof := test_sortof
}.

Definition test_GCS :=
  <GCS [p 1; p 2; p 3] [d 1; d 2; d 3]
    <CONSTRAINT dist_pp (p 1) (p 2) (d 1)>
    <CONSTRAINT dist_pp (p 2) (p 3) (d 2)>
    <CONSTRAINT dist_pp (p 3) (p 1) (d 3)> >.

Print test_GCS.



