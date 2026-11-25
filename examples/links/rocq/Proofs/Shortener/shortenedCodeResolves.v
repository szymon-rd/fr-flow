Require Export FrFlowGen.Shortener.shortenedCodeResolves.Spec.
Require Export Proofs.Shortener.Lemmas.

(** The code a URL is given leads to it: a code given again led to it already, and a new code's link is put
    first. *)
Lemma shortenedCodeResolves_Proofs_impl : shortenedCodeResolves_Obl_impl.
Proof.
  unfold shortenedCodeResolves_Obl_impl, shortenedCodeResolves_claim.
  intros s u.
  destruct (Lemmas_shorten_cases s u) as [[l [_ [hl e]]] | [_ [k [_ e]]]]; rewrite e; cbn [fst snd].
  - exact hl.
  - rewrite Lemmas_resolve_cons. rewrite ite_true by reflexivity. reflexivity.
Qed.
