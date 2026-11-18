Require Export FrFlowGen.FullShortener.shortenKeepsExistingLinks.Spec.
Require Export Proofs.FullShortener.Lemmas.

(** Shortening never changes where a code that leads somewhere leads: a code given again changes nothing, and a
    new code is none of the codes given, so none that leads anywhere. *)
Lemma shortenKeepsExistingLinks_Proofs_impl : shortenKeepsExistingLinks_Obl_impl.
Proof.
  unfold shortenKeepsExistingLinks_Obl_impl, shortenKeepsExistingLinks_claim.
  intros s u c defined.
  destruct (Lemmas_shorten_cases s u) as [[l [_ [_ e]]] | [_ [k [fresh e]]]]; rewrite e; cbn [snd];
    [reflexivity |].
  rewrite Lemmas_resolve_cons. destruct (classic (k = c)) as [h | h].
  - exfalso. destruct (Lemmas_resolve_some s c defined) as [l [i hc]].
    apply (fresh (Link_code l)); [| rewrite hc; exact h].
    apply in_or_app. left. unfold List_map. apply in_map. exact i.
  - rewrite (ite_false _ _ _ h). reflexivity.
Qed.
