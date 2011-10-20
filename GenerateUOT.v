Require Export Containers.OrderedType.

(**
 * Containers.Generate produces OrderedType instances, but for sorts we
 * specifically need the Liebnitz equality. Fortunately, for simple types
 * the generated equality is equivalent. This library registers a tactic
 * which will automatically convert the generated OrderedType into a
 * UsualOrderType when this is the case.
 *)

Instance usualify_OrderedType `(OT : OrderedType)
  (H_eq : forall x y : A, _eq x y <-> x = y) : UsualOrderedType A :=
{
  SOT_lt := _lt;
  SOT_cmp := _cmp
}.
Proof.
  split.

  apply StrictOrder_Transitive.

  intros x y Hxy Hxy'.
  unfold equiv in Hxy'.
  rewrite <- H_eq in Hxy'.
  apply (StrictOrder_Irreflexive x y Hxy Hxy').

  intros x y.
  case (compare_dec x y); intro Hxy.
  apply compare_spec_lt, Hxy.
  unfold equiv in Hxy; rewrite H_eq in Hxy.
  apply compare_spec_eq, Hxy.
  apply compare_spec_gt, Hxy.
Defined.

Ltac reinforce_generated_OrderedType :=
  eapply usualify_OrderedType;
  split; [ intro H; induction H; reflexivity |
	   intro H; rewrite H; reflexivity ].

Hint Extern 10 (SpecificOrderedType _ eq _) =>
  reinforce_generated_OrderedType : typeclass_instances.
