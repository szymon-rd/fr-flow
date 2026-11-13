Require Export FrFlowGen.Shop.placedAgainIsDuplicate.Spec.

(** An order sent again is a duplicate. However the first call ended, it registered the order, or found it
    registered, and recording how an order ended leaves the registrations as they are; so the second call does not
    win its registration. *)
Lemma placedAgainIsDuplicate_Proofs_impl : placedAgainIsDuplicate_Obl_impl.
Proof.
  intros register reserve settle charge release registered hOnce hStays hSettle checkout o _.
  unfold registerIsWonOnce_claim, registeredStaysRegistered_claim, settleKeepsRegistered_claim in *.
  assert (again : registered
    (Checkout_orders (snd (shopCheckout_place register reserve settle charge release checkout o))) (Order_id_ o)).
  { unfold shopCheckout_place; cbv zeta.
    repeat match goal with |- context [ite ?P _ _] => frflow_case P end; cbn;
      repeat rewrite hSettle; apply hStays; left; reflexivity. }
  generalize dependent (snd (shopCheckout_place register reserve settle charge release checkout o)).
  intros placed again. unfold shopCheckout_place; cbv zeta; cbn.
  rewrite (ite_true (~ fst (register (Checkout_orders placed) (Order_id_ o)))); [reflexivity |].
  rewrite hOnce. tauto.
Qed.
