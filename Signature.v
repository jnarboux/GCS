Require Import List.
Require Export Containers.OrderedType.

Set Implicit Arguments.
Unset Strict Implicit.

(**
 * Many-sorted signature.
 *)
Class Signature := {
  sort : Type;
  sort_UOT :> UsualOrderedType sort;
  pred : Type;
  pred_ar : pred -> list sort
}.

(* An arity (in the extended sense) is a list of sorts. *)
Notation arity := (list sort).

(* A "domain" affect a type to each sort. *)
Definition domain `{sigma : Signature} := sort -> Type.

(* Functions from one domain to another. *)
Notation "E ~> E'" := (forall s : sort, E s -> E' s) (at level 90).

(**
 * Given a domain and an arity, we define the type of corresponding lists.
 *)
Section arities.
  Context {sigma : Signature}.

  (* Argument lists *)
  Inductive arglist (E : domain) : arity -> Type :=
    | argnil :
        arglist E nil
    | argcons :
        forall {s}, E s ->
        forall {ar}, arglist E ar ->
        arglist E (s::ar).

  Implicit Arguments argnil [E].

  Fixpoint argmap {E E'} (f : E ~> E')
                  {ar} (args : arglist E ar) : arglist E' ar :=
    match args with
      | argnil => argnil
      | argcons s arg ar args => argcons (f s arg) (argmap f args)
    end.

  Fixpoint argfold {E : domain} {A : arity -> Type}
      (f : forall s, E s -> forall ar, A ar -> A (s::ar)) (Anil : A nil)
      {ar} (args : arglist E ar) : (A ar) :=
    match args with
      | argnil => Anil
      | argcons s arg ar args => f _ arg _ (argfold f Anil args)
    end.

  (* Sanity check *)
  Let arglist_dup_works E ar (args : arglist E ar) :
    argfold (@argcons E) argnil args = args.
  Proof.
    induction args.
    reflexivity.
    simpl.
    rewrite IHargs.
    reflexivity.
  Qed.
End arities.

Implicit Arguments argnil [sigma E].
Notation "[ x ; .. ; y ]" := (argcons x .. (argcons y argnil) ..).
