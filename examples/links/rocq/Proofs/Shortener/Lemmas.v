Require Export FrFlowGen.Shortener.Domain.

(** What the proofs of the shortener share: what finding in a list gives, what filtering out a code leaves to find,
    that the number a new code is given is above every code it is computed from, and the two cases of shortening. *)

(** What a find gives is in the list and meets the condition. *)
Lemma Lemmas_find_some {A : Type} (p : A -> Prop) (xs : list A) (x : A) :
  List_find p xs = Some x -> In x xs /\ p x.
Proof.
  induction xs as [| y ys ih]; intros h; [discriminate |].
  rewrite List_find_cons in h. destruct (classic (p y)) as [py | npy].
  - rewrite (ite_true _ _ _ py) in h. injection h as <-. split; [left; reflexivity | exact py].
  - rewrite (ite_false _ _ _ npy) in h. destruct (ih h) as [i px]. split; [right; exact i | exact px].
Qed.

(** A find that gives nothing: no member meets the condition. *)
Lemma Lemmas_find_none {A : Type} (p : A -> Prop) (xs : list A) :
  List_find p xs = None -> forall x, In x xs -> ~ p x.
Proof.
  induction xs as [| y ys ih]; intros h x i; [destruct i |].
  rewrite List_find_cons in h. destruct (classic (p y)) as [py | npy].
  - rewrite (ite_true _ _ _ py) in h. discriminate.
  - rewrite (ite_false _ _ _ npy) in h. destruct i as [<- | i]; [exact npy | exact (ih h x i)].
Qed.

(** A find whose first member meets the condition gives it. *)
Lemma Lemmas_find_head {A : Type} (p : A -> Prop) (x : A) (xs : list A) : p x -> List_find p (x :: xs) = Some x.
Proof. intros h. rewrite List_find_cons. exact (ite_true _ _ _ h). Qed.

(** With the links of one code filtered out, the first link of another code is the one it was. *)
Lemma Lemmas_find_filter_other (xs : list Link) (c d : Code) :
  c <> d ->
  List_find (fun l => Link_code l = d) (List_filter (fun l => ~ Link_code l = c) xs) =
    List_find (fun l => Link_code l = d) xs.
Proof.
  intros cd. induction xs as [| x xs ih]; [reflexivity |].
  rewrite List_filter_cons. destruct (classic (Link_code x = c)) as [xc | xc].
  - assert (nk : ~ ~ Link_code x = c) by (intros n; exact (n xc)).
    rewrite (ite_false _ _ _ nk). rewrite ih. rewrite List_find_cons.
    assert (xd : ~ Link_code x = d) by (intros e; apply cd; rewrite <- xc; exact e).
    rewrite (ite_false _ _ _ xd). reflexivity.
  - rewrite (ite_true _ _ _ xc). rewrite !List_find_cons. rewrite ih. reflexivity.
Qed.

(** With the links of a code filtered out, no link of that code is found. *)
Lemma Lemmas_find_filter_same (xs : list Link) (c : Code) :
  List_find (fun l => Link_code l = c) (List_filter (fun l => ~ Link_code l = c) xs) = None.
Proof.
  induction xs as [| x xs ih]; [reflexivity |].
  rewrite List_filter_cons. destruct (classic (Link_code x = c)) as [xc | xc].
  - assert (nk : ~ ~ Link_code x = c) by (intros n; exact (n xc)).
    rewrite (ite_false _ _ _ nk). exact ih.
  - rewrite (ite_true _ _ _ xc). rewrite List_find_cons. rewrite (ite_false _ _ _ xc). exact ih.
Qed.

(** The step the shortener's number is computed by keeps what it has so far, and goes above the code it reads. *)
Lemma Lemmas_above_step (top : Z) (c : Code) :
  top <= ite (top <= Code_number c) (Code_number c + 1) top /\
    Code_number c < ite (top <= Code_number c) (Code_number c + 1) top.
Proof.
  destruct (classic (top <= Code_number c)) as [h | h].
  - rewrite (ite_true _ _ _ h). lia.
  - rewrite (ite_false _ _ _ h). lia.
Qed.

Lemma Lemmas_fold_ge (xs : list Code) (init : Z) :
  init <= List_foldl (fun top c => ite (top <= Code_number c) (Code_number c + 1) top) init xs.
Proof.
  revert init. induction xs as [| x xs ih]; intros init; [reflexivity |].
  rewrite List_foldl_cons. cbv beta. pose proof (Lemmas_above_step init x) as [h _].
  specialize (ih (ite (init <= Code_number x) (Code_number x + 1) init)). lia.
Qed.

(** The number computed is above every code it is computed from, so a code made of it is none of them. *)
Lemma Lemmas_fresh (xs : list Code) (init : Z) (x : Code) :
  In x xs -> Code_mk (List_foldl (fun top c => ite (top <= Code_number c) (Code_number c + 1) top) init xs) <> x.
Proof.
  intros i. revert init. induction xs as [| y ys ih]; intros init e; [destruct i |].
  rewrite List_foldl_cons in e. cbv beta in e. destruct i as [<- | i].
  - pose proof (Lemmas_above_step init y) as [_ h].
    pose proof (Lemmas_fold_ge ys (ite (init <= Code_number y) (Code_number y + 1) init)) as g.
    apply (f_equal Code_number) in e. cbn [Code_number] in e. lia.
  - exact (ih i _ e).
Qed.

(** Removing a code filters out its links and keeps it among those removed. *)
Lemma Lemmas_remove (s : Links) (c : Code) :
  snd (retiringLinks_remove s c) =
    Links_mk (List_filter (fun l => ~ Link_code l = c) (Links_issued s)) (c :: Links_retired s).
Proof. reflexivity. Qed.

(** A new link first leads its code to its URL; any other code leads where it did. *)
Lemma Lemmas_resolve_cons (k : Code) (u : Url) (xs : list Link) (r : list Code) (c : Code) :
  retiringLinks_resolve (Links_mk (Link_mk k u :: xs) r) c =
    ite (k = c) (Some u) (retiringLinks_resolve (Links_mk xs r) c).
Proof.
  unfold retiringLinks_resolve, decide. cbn. rewrite List_find_cons. cbn.
  destruct (classic (k = c)) as [h | h].
  - rewrite !(ite_true _ _ _ h). reflexivity.
  - rewrite !(ite_false _ _ _ h). reflexivity.
Qed.

(** A code that leads somewhere is the code of a link. *)
Lemma Lemmas_resolve_some (s : Links) (c : Code) :
  retiringLinks_resolve s c <> None -> exists l, In l (Links_issued s) /\ Link_code l = c.
Proof.
  unfold retiringLinks_resolve, decide. cbn. intros h.
  destruct (List_find (fun l => Link_code l = c) (Links_issued s)) as [l |] eqn:hf; [| contradiction].
  exists l. exact (Lemmas_find_some _ _ _ hf).
Qed.

(** Shortening a URL, in its two cases: a code that leads to it already is given, and nothing changes; or none
    does, and a code that is none of those given or removed is given, its link put first. *)
Lemma Lemmas_shorten_cases (s : Links) (u : Url) :
  (exists l, In l (Links_issued s) /\ retiringLinks_resolve s (Link_code l) = Some u /\
     retiringLinks_shorten s u = (Link_code l, s)) \/
  ((forall l, In l (Links_issued s) -> retiringLinks_resolve s (Link_code l) <> Some u) /\
     exists k, (forall x, In x (List_map Link_code (Links_issued s) ++ Links_retired s) -> k <> x) /\
       retiringLinks_shorten s u = (k, Links_mk (Link_mk k u :: Links_issued s) (Links_retired s))).
Proof.
  unfold retiringLinks_shorten, Option_getD, decide. cbv zeta. cbn.
  match goal with |- context [List_find ?p (Links_issued s)] =>
    destruct (List_find p (Links_issued s)) as [l |] eqn:hk end.
  - left. exists l. apply Lemmas_find_some in hk. destruct hk as [i hp].
    split; [exact i |]. split; [exact hp |].
    rewrite (ite_false False) by tauto. reflexivity.
  - right. split.
    + intros l i. exact (Lemmas_find_none _ _ hk l i).
    + eexists. split; [| rewrite (ite_true True) by exact I; reflexivity].
      intros x i. apply Lemmas_fresh. exact i.
Qed.

(** Shortening the URL of the first link gives its code, and changes nothing. *)
Lemma Lemmas_shorten_first (k : Code) (u : Url) (xs : list Link) (r : list Code) :
  retiringLinks_shorten (Links_mk (Link_mk k u :: xs) r) u = (k, Links_mk (Link_mk k u :: xs) r).
Proof.
  unfold retiringLinks_shorten, Option_getD, decide. cbv zeta. cbn.
  erewrite Lemmas_find_head.
  - cbn. rewrite (ite_false False) by tauto. reflexivity.
  - cbn. erewrite Lemmas_find_head; reflexivity.
Qed.
