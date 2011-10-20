Require Import Syntax.

(* Extensive notation for sets *)
Notation "[ x1 ; .. ; xn ]" :=
  (add x1 .. (add xn (@empty _ _ variable_FS)) ..) : set_scope.

(* Helper functions to build arglists at parse time *)
Section package_arglist.
  Context `{env : Environment} (V : VS).

  Program Fixpoint package_arglist (lS : list sort) (l : list variable) :
    option (arglist V lS) :=
        match lS, l with
          | nil, nil => Some argnil
          | nil, v::l => None
          | s::lS, nil => None
          | s::lS, v::l =>
            match package_arglist lS l with
              | Some argl => _
              | None => None
            end
        end.
  Next Obligation.
    case_eq (sortof v == s).
    2: intros _; exact None.

    intro Hs.
    assert (Hs' : sortof v = s).
      case (eq_dec (sortof v) s).
      tauto.
      intro Hs'; exfalso.
      pose proof (eq_dec (sortof v) s) as Hs''.
      rewrite Hs in Hs''.
      inversion Hs''.
      elim (Hs' H).

    case_eq (mem v V).
    2: intros _; exact None.

    intro Hv.
    apply mem_2 in Hv.
    apply Some, argcons.
    exact (Build_variable_in _ _ V s v Hs' Hv).
    exact a.
  Defined.

  Fixpoint package_constraints (C : list (pred * list variable)) :
    option (list (formula V)) :=
      match C with
        | nil => Some nil
        | (p, l)::C =>
          match package_constraints C with
            | Some C' => 
              match package_arglist (pred_ar p) l with
                | Some args =>  Some ((pred_apply p args) :: C')
                | None => None
              end
            | None => None
          end
      end.

  Definition package_arglist_succeeds lS l :=
    package_arglist lS l <> None.

  Definition package_arglist_extract lS l :
    package_arglist_succeeds lS l -> arglist V lS.
  Proof.
    intro H.
    case_eq (package_arglist lS l).
    intros a _; exact a.
    intros H'; elim (H H').
  Defined.

  Definition package_extract {T} (x : option T) (H : x <> None) : T.
    induction x as [t|].
    exact t.
    elim H; reflexivity.
  Defined.

  Lemma assert_package_success {T} (t : T) : Some t <> None.
  Proof.
    discriminate.
  Qed.

  Definition VS_is_empty := is_empty V.
  Definition VS_is_empty_2 (H : VS_is_empty = true) := is_empty_2 H.
  Definition VS_union (V' : VS) : VS := V ++ V'.
  Definition VS_inter (V' : VS) : VS := inter V V'.
End package_arglist.

(*
Definition VS_is_empty `{env : Environment} (V : VS) :=
  is_empty V.
Definition VS_is_empty_2 `{env : Environment} {V : VS} :
  VS_is_empty V = true -> Empty V := @is_empty_2 _ _ _ _ V.
Definition VS_union `{env : Environment} (V1 V2 : VS) : VS := V1 ++ V2.
*)

Notation "<ARGLIST V lS l >" :=
  (package_extract (package_arglist V lS l) (assert_package_success _))
  (V at level 0, lS at level 0, l at level 0).

Notation "<FORMULA V pl >" :=
  (pred_apply (fst pl) <ARGLIST V (pred_ar (fst pl)) (snd pl)>)
  (V at level 0, pl at level 0).

Notation "<DISJOINT X A >" :=
  (VS_is_empty_2 _ (refl_equal true : VS_is_empty (VS_inter X A) = true))
  (X at level 0, A at level 0).

Notation "<CONSTRAINT p arg1 .. argn >" :=
  (pair p (cons arg1 .. (cons argn nil) ..))
  (p at level 0, arg1 at level 0, argn at level 0).

Notation "<GCS X A c1 .. cn >" :=
  (Build_GCS X A <DISJOINT X A>
    (package_extract
       (package_constraints
          (VS_union X A)
          (cons c1 .. (cons cn nil) ..))
       (assert_package_success _)))
  (X at level 0, A at level 0, c1 at level 0, cn at level 0).
