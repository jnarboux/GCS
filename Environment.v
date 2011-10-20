Require Export Containers.Sets.
Require Export Signature.

(**
 * An environment defines the type of variables and the sort of each one.
 *)
Class Environment `(sigma : Signature) := {
  variable : Type;
  variable_OT :> OrderedType variable;
  variable_FS :> FSet;
  variable_FS_specs :> FSetSpecs variable_FS;
  sortof : variable -> sort
}.

(**
 * Sets of variables.
 *)
Definition VS `{env : Environment} := set variable.
Bind Scope set_scope with VS.

(**
 * Variable in a set, of a given sort.
 *)
Record variable_in `{env : Environment} (V : VS) (s : sort) := {
  variable_in_proj :> variable;
  variable_in_sort : sortof variable_in_proj = s;
  variable_in_set : In variable_in_proj V
}.

(* variable_in allows us to use set of variables as domains, which
 * associate to each sort the subset of variables of this sort. *)
Coercion variable_in : VS >-> Funclass.
