Require Export FrFlowGen.Sets.whoIsAddedStays.Spec.
Require Export Proofs.Sets.Lemmas.

(** Nothing is called before the run starts. *)
Lemma none_called_before_the_start (steps : Z -> Step) c who m :
  (forall w, w < 0 -> steps w = Step_Rests) -> m < 0 -> ~ calledBy steps c who m.
Proof.
  intros Hstart Hm Hc. assert (steps m = Step_Rests) as E by (apply Hstart; exact Hm).
  destruct Hc as [(inside & Hc) | (a & inside & hands & Hc)]; rewrite E in Hc; discriminate.
Qed.

(** A completed call of what is atomic was made one moment before. *)
Lemma atomic_completes_next (steps : Z -> Step) c who from answer to :
  (forall w who, calledBy steps c who w -> exists a, doneAtOnce steps c who w a) ->
  completedBy steps c who from answer to -> to = from + 1 /\ calledBy steps c who from.
Proof.
  intros Hatomic [[Hdone ->] | [Hbegun _]].
  - split; [reflexivity | right; exists answer; exact Hdone].
  - destruct (Hatomic from who (or_introl Hbegun)) as (a & inside & hands & Hdoes).
    destruct Hbegun as (inside' & Hmakes). rewrite Hmakes in Hdoes. discriminate.
Qed.

Lemma whoIsAddedStays_Proofs_complete : whoIsAddedStays_Obl_complete.
Proof.
  intros elements steps Hatomic Hadd Hrem Honly Hstart s t w.
  destruct (Z_lt_le_dec w 0) as [Hneg | Hpos].
  { intros [(m & Hm & who & Hc) _]. exfalso.
    eapply (none_called_before_the_start steps); [exact Hstart | | exact Hc]; lia. }
  revert w Hpos. apply (natlike_ind (fun w => _ -> elements s w t)).
  { intros [(m & Hm & who & Hc) _]. exfalso.
    eapply (none_called_before_the_start steps); [exact Hstart | | exact Hc]; lia. }
  intros w Hw IH [(m & Hm & who & Hc) Hno]. unfold Z.succ in *.
  assert (m = w \/ m < w) as [-> | Hlt] by lia.
  - destruct (proj1 (Hatomic s t) w who Hc) as (a & Hdone).
    rewrite (Hadd s t t w a (w + 1)); [left; reflexivity |].
    exists who. left. split; [exact Hdone | reflexivity].
  - assert (elements s w t) as Hin.
    { apply IH. split; [exists m; split; [exact Hlt | exists who; exact Hc] |].
      intros (m' & Hm' & Hc'). apply Hno. exists m'. split; [lia | exact Hc']. }
    destruct (classic (elements s (w + 1) t)) as [H | Hout]; [exact H | exfalso].
    destruct (Honly s w (w + 1) t) as (x & [Hx | Hx]).
    { split; [lia |]. intros E. apply Hout. rewrite <- E. exact Hin. }
    + destruct Hx as (a & answer & b & [Ha Hb] & who' & Hdone).
      destruct (atomic_completes_next steps _ who' a answer b (proj1 (Hatomic s x)) Hdone) as [-> _].
      assert (a = w) as -> by lia. apply Hout.
      rewrite (Hadd s x t w answer (w + 1)); [right; exact Hin | exists who'; exact Hdone].
    + destruct Hx as (a & answer & b & [Ha Hb] & who' & Hdone).
      destruct (atomic_completes_next steps _ who' a answer b (proj2 (Hatomic s x)) Hdone) as [-> Hcalled].
      assert (a = w) as -> by lia.
      destruct (classic (t = x)) as [<- | Hne].
      * apply Hno. exists w. split; [lia | exists who'; exact Hcalled].
      * apply Hout. rewrite (Hrem s x t w answer (w + 1)); [split; assumption | exists who'; exact Hdone].
Qed.

(** The assumptions do not contradict each other: a run in which nothing happens meets them. *)
Lemma whoIsAddedStays_Proofs_feasible : whoIsAddedStays_Obl_feasible.
Proof.
  first [ exists (fun _ _ _ => False), (fun _ => Step_Rests) | exists (fun _ => Step_Rests), (fun _ _ _ => False) ].
  repeat split.
  - intros w who H. destruct (nothing_called_at_rest _ _ _ H).
  - intros w who H. destruct (nothing_called_at_rest _ _ _ H).
  - intros s x y from answer to (who & H). destruct (nothing_completed_at_rest _ _ _ _ _ H).
  - intros s x y from answer to (who & H). destruct (nothing_completed_at_rest _ _ _ _ _ H).
  - intros s a b y [_ H]. destruct H. reflexivity.
Qed.
