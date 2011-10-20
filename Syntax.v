Require Export Environment.
Require Import SetDecide.

Section Syntax.
  Context `{env : Environment}.

  Inductive formula (V : VS) :=
    | pred_apply (p : pred) : arglist V (pred_ar p) -> formula V.

  Parameter generalize :
    forall {V V' : VS} (H : V [<=] V'),
      formula V -> formula V'.

  Record GCS := {
    unknowns : VS;
    parameters : VS;
    disjoint : Empty (inter unknowns parameters);
    variables := unknowns ++ parameters;
    constraints : list (formula variables)
  }.

  Section sum.
    Variable S1 S2 : GCS.

    Let X := unknowns S1 ++ unknowns S2.
    Let A := (parameters S1 ++ parameters S2) \ X.

    Program Definition sum : GCS := {|
      unknowns := X;
      parameters := A;
      constraints :=
        app (map (generalize _) (constraints S1))
            (map (generalize _) (constraints S2))
    |}.
    Let inter_diff_empty :
      forall V V' : VS, Empty (inter (V) (V' \ V)).
    Proof.
      intros V V' v Hv.
      pose proof (inter_1 Hv) as Hv1.
      pose proof (inter_2 Hv) as Hv2.
      apply diff_2 in Hv2.
      tauto.
    Qed.
    Next Obligation.
      apply inter_diff_empty.
    Qed.
    Let vars_is_union :
      X ++ A [=] variables S1 ++ variables S2.
    Proof.
      unfold variables, A, X.
      destruct S1 as [X1 A1 H1 V1 C1].
      destruct S2 as [X2 A2 H2 V2 C2].
      simpl.
      clear X A H1 V1 C1 H2 V2 C2 S1 S2.
      unfold VS in *.
      intro v.
      repeat rewrite mem_iff.
      repeat rewrite union_b.
      rewrite diff_b.
      repeat rewrite union_b.
      case (v \in X1);
      case (v \in X2);
      case (v \in A1);
      case (v \in A2);
      simpl;
      reflexivity.
    Qed.
    Next Obligation.
      rewrite vars_is_union.
      intro v.
      apply union_2.
    Qed.
    Next Obligation.
      rewrite vars_is_union.
      intro v.
      apply union_3.
    Qed.
  End sum.
End Syntax.

Implicit Arguments pred_apply [sigma env V].
