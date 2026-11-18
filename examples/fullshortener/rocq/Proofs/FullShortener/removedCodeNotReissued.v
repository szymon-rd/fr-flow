Require Export FrFlowGen.FullShortener.removedCodeNotReissued.Spec.
Require Export Proofs.FullShortener.Lemmas.

(** A code just removed is kept as removed, and is the code of no link. *)
Lemma removedCodeNotReissued_gone_removed (s : Links) (code : Code) :
  In code (Links_retired (snd (retiringLinks_remove s code))) /\
    (forall l, In l (Links_issued (snd (retiringLinks_remove s code))) -> Link_code l <> code).
Proof.
  change (snd (retiringLinks_remove s code)) with
    (Links_mk (List_filter (fun l => ~ Link_code l = code) (Links_issued s)) (code :: Links_retired s)).
  split; [left; reflexivity |].
  intros l i. cbn [Links_issued] in i. apply List_filter_In in i. destruct i as [_ h]. exact h.
Qed.

(** Shortening a URL keeps a code that is kept as removed, and the code of no link, so. *)
Lemma removedCodeNotReissued_gone_shorten (s : Links) (u : Url) (code : Code) :
  In code (Links_retired s) /\ (forall l, In l (Links_issued s) -> Link_code l <> code) ->
  In code (Links_retired (snd (retiringLinks_shorten s u))) /\
    (forall l, In l (Links_issued (snd (retiringLinks_shorten s u))) -> Link_code l <> code).
Proof.
  intros [retired none].
  destruct (Lemmas_shorten_cases s u) as [[l [_ [_ e]]] | [_ [k [fresh e]]]]; rewrite e; cbn [snd];
    [split; assumption |].
  split; [exact retired |].
  intros l [<- | i]; [| exact (none l i)].
  cbn [Link_code]. apply fresh. apply in_or_app. right. exact retired.
Qed.

(** Removing a code keeps a code that is kept as removed, and the code of no link, so. *)
Lemma removedCodeNotReissued_gone_remove (s : Links) (d code : Code) :
  In code (Links_retired s) /\ (forall l, In l (Links_issued s) -> Link_code l <> code) ->
  In code (Links_retired (snd (retiringLinks_remove s d))) /\
    (forall l, In l (Links_issued (snd (retiringLinks_remove s d))) -> Link_code l <> code).
Proof.
  intros [retired none].
  change (snd (retiringLinks_remove s d)) with
    (Links_mk (List_filter (fun l => ~ Link_code l = d) (Links_issued s)) (d :: Links_retired s)).
  split; [right; exact retired |].
  intros l i. cbn [Links_issued] in i. apply List_filter_In in i. destruct i as [i _]. exact (none l i).
Qed.

(** A code kept as removed, and the code of no link, is not the code a URL is given. *)
Lemma removedCodeNotReissued_gone_not_given (s : Links) (u : Url) (code : Code) :
  In code (Links_retired s) /\ (forall l, In l (Links_issued s) -> Link_code l <> code) ->
  fst (retiringLinks_shorten s u) <> code.
Proof.
  intros [retired none].
  destruct (Lemmas_shorten_cases s u) as [[l [i [_ e]]] | [_ [k [fresh e]]]]; rewrite e; cbn [fst].
  - exact (none l i).
  - apply fresh. apply in_or_app. right. exact retired.
Qed.

(** A removed code is never given to a URL again: once removed it is kept as removed and is the code of no link,
    which every later call keeps so; and such a code is neither one given again nor a new one. *)
Lemma removedCodeNotReissued_Proofs_impl : removedCodeNotReissued_Obl_impl.
Proof.
  unfold removedCodeNotReissued_Obl_impl, removedCodeNotReissued_claim.
  intros s code url later. apply removedCodeNotReissued_gone_not_given.
  apply (Lemmas_fold_keeps (fun st => In code (Links_retired st) /\
    (forall l, In l (Links_issued st) -> Link_code l <> code))).
  - intros st call gone. destruct call as [given | other].
    + apply removedCodeNotReissued_gone_shorten. exact gone.
    + apply removedCodeNotReissued_gone_remove. exact gone.
  - apply removedCodeNotReissued_gone_removed.
Qed.
