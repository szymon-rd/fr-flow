Require Export FrFlowGen.FullShortener.shortenIsIdempotent.Spec.
Require Export Proofs.FullShortener.Lemmas.

(** Shortening a URL a second time gives the code it gave and changes nothing: a code given again changed nothing
    the first time either, and a new code's link is the first the second call finds. *)
Lemma shortenIsIdempotent_Proofs_impl : shortenIsIdempotent_Obl_impl.
Proof.
  unfold shortenIsIdempotent_Obl_impl, shortenIsIdempotent_claim.
  intros s u.
  destruct (Lemmas_shorten_cases s u) as [[l [_ [_ e]]] | [_ [k [_ e]]]]; rewrite e; cbn [fst snd].
  - rewrite e. split; reflexivity.
  - rewrite Lemmas_shorten_first. split; reflexivity.
Qed.
