Require Export FrFlowGen.Shop.chargeKeepsOrderly.Spec.

(** Charging an order leaves the books orderly about every order. The claim of the order's payment leaves every
    posting as it is and every payment claimed that was, and claims the order's own. The charge that may follow
    posts for its own order only, whose payment is then claimed, and leaves the claims as they are. *)
Lemma chargeKeepsOrderly_Proofs_impl : chargeKeepsOrderly_Obl_impl.
Proof.
  intros postingsOf claimed claim chargeIfCovered hKeeps hStays hClaims hPosts payments order o sensible premise.
  unfold claimKeepsPostings_claim, claimedStaysClaimed_claim, chargeKeepsClaims_claim,
    chargePostsItsOrder_claim in *.
  unfold ledgerPayments_charge, ledgerPayments_ledger_held; cbv zeta; cbn.
  frflow_case (~ fst (claim (Payments_ledger payments) (Order_id_ o))); cbn.
  - destruct premise as [e | c]; [left; rewrite hKeeps; exact e | right; apply hStays; right; exact c].
  - destruct (classic (order = Order_id_ o)) as [e | other].
    + right. rewrite (hClaims _ _ _ sensible). apply hStays. left. exact e.
    + destruct premise as [e | c].
      * left. rewrite (hPosts _ _ _ sensible other). rewrite hKeeps. exact e.
      * right. rewrite (hClaims _ _ _ sensible). apply hStays. right. exact c.
Qed.
