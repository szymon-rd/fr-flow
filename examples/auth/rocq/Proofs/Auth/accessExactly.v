Require Export FrFlowGen.Auth.accessExactly.Spec.
Require Export Proofs.Auth.Lemmas.

(** A user gets access exactly when signed in and authorized: a session's token admitted on their behalf is
    theirs, with a grant for the path; and a session of theirs, with a grant, has its token admitted for them. *)
Lemma accessExactly_Proofs_complete : accessExactly_Obl_complete.
Proof.
  intros access signedIn authorized grants sessions admit hs hgt hst hreq htn han hgl u r.
  rewrite (hreq hs u r), (hst hs u), (hgt u r). apply propositional_extensionality.
  unfold admittedTo. split.
  - intros [s [hm ha]]. pose proof (htn hs (token_of s) r u ha) as hh.
    rewrite (Lemmas_holder_of_session sessions hs s hm) in hh. injection hh as hh. split.
    + exists s. split; [exact hm | exact hh].
    + exact (han (token_of s) r u ha).
  - intros [[s [hm hu]] hg]. subst u. exists s. split; [exact hm |].
    pose proof (Lemmas_holder_of_session sessions hs s hm) as hh.
    transitivity (holderOf sessions (token_of s)); [| exact hh]. apply (hgl hs).
    exists (user_of s). split; [exact hh | exact hg].
Qed.
