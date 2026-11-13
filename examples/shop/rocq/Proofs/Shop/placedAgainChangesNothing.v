Require Export FrFlowGen.Shop.placedAgainChangesNothing.Spec.

(** An order sent again leaves the shop as the first call left it. However the first call ended, it registered the
    order, or found it registered; so the second call does not win its registration, and a registration not won
    leaves the order book as it is: the second call does nothing more. *)
Lemma placedAgainChangesNothing_Proofs_impl : placedAgainChangesNothing_Obl_impl.
Proof.
  intros register reserve settle charge release registered hOnce hStays hLost hSettle checkout o _.
  unfold registerIsWonOnce_claim, registeredStaysRegistered_claim, lostRegisterChangesNothing_claim,
    settleKeepsRegistered_claim in *.
  assert (again : registered
    (Checkout_orders (snd (shopCheckout_place register reserve settle charge release checkout o))) (Order_id_ o)).
  { unfold shopCheckout_place; cbv zeta.
    repeat match goal with |- context [ite ?P _ _] => frflow_case P end; cbn;
      repeat rewrite hSettle; apply hStays; left; reflexivity. }
  generalize dependent (snd (shopCheckout_place register reserve settle charge release checkout o)).
  intros placed again. unfold shopCheckout_place; cbv zeta; cbn.
  assert (lost : ~ fst (register (Checkout_orders placed) (Order_id_ o))) by (rewrite hOnce; tauto).
  rewrite (ite_true _ _ _ lost). cbn. rewrite (hLost _ _ lost). destruct placed; reflexivity.
Qed.
