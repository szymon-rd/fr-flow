Require Export FrFlowGen.Shop.chargePostsOnce.Spec.

(** Charging an order makes no posting of another order, nor of one whose payment is claimed. The claim of the
    order's payment leaves every posting as it is. If it is lost, nothing more is done. If it is won, the payment
    was not claimed, so the order asked of is another, and the charge posts for its own order only. *)
Lemma chargePostsOnce_Proofs_impl : chargePostsOnce_Obl_impl.
Proof.
  intros claimed postingsOf claim chargeIfCovered hKeeps hOnce hPosts payments order o sensible premise.
  unfold claimKeepsPostings_claim, claimIsWonOnce_claim, chargePostsItsOrder_claim in *.
  unfold ledgerPayments_charge, ledgerPayments_ledger_held; cbv zeta; cbn.
  frflow_case (~ fst (claim (Payments_ledger payments) (Order_id_ o))); cbn.
  - apply hKeeps.
  - assert (other : order <> Order_id_ o).
    { intro e. subst order. destruct premise as [n | c]; [apply n; reflexivity |].
      apply h. rewrite hOnce. intro nc. exact (nc c). }
    rewrite (hPosts _ _ _ sensible other). apply hKeeps.
Qed.
