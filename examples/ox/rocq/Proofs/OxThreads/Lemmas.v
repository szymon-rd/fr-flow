Require Export FrFlowGen.OxThreads.Domain.

(** ** The moments from one on *)

Lemma from_a_moment_on (P : Z -> Prop) (m : Z) :
  P m -> (forall k, m <= k -> P k -> P (k + 1)) -> forall k, m <= k -> P k.
Proof.
  intros Hm Hstep k Hk. replace k with (m + (k - m)) by lia.
  apply (natlike_ind (fun d => P (m + d))); [replace (m + 0) with m by lia; exact Hm | | lia].
  intros d Hd IH. replace (m + Z.succ d) with (m + d + 1) by lia. apply Hstep; [lia | exact IH].
Qed.

(** ** One step from each moment *)

Lemma none_called_before_the_start (steps : Z -> Step) c who m :
  (forall w, w < 0 -> steps w = Step_Rests) -> m < 0 -> ~ calledBy steps c who m.
Proof.
  intros Hstart Hm Hc. assert (steps m = Step_Rests) as E by (apply Hstart; exact Hm).
  destruct Hc as [(inside & Hc) | (a & inside & hands & Hc)]; rewrite E in Hc; discriminate.
Qed.

(** What is called at a moment is one call, by one actor. *)
Lemma one_call_at_a_moment (steps : Z -> Step) c1 c2 who1 who2 w :
  calledBy steps c1 who1 w -> calledBy steps c2 who2 w -> c1 = c2 /\ who1 = who2.
Proof.
  intros [(i1 & H1) | (a1 & i1 & h1 & H1)] [(i2 & H2) | (a2 & i2 & h2 & H2)]; rewrite H1 in H2;
    try discriminate; injection H2; intros; subst; split; reflexivity.
Qed.

Lemma begun_is_called (steps : Z -> Step) c who w : begun steps c who w -> calledBy steps c who w.
Proof. intros H. left. exact H. Qed.

Lemma completed_was_called (steps : Z -> Step) c who from answer to :
  completedBy steps c who from answer to -> calledBy steps c who from.
Proof. intros [[Hdone _] | [Hbegun _]]; [right; exists answer; exact Hdone | left; exact Hbegun]. Qed.

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

Lemma over_later (steps : Z -> Step) who from a b : a <= b -> overBy steps who from a -> overBy steps who from b.
Proof. intros Hab (k & ans & hands & Hk & Hs). exists k, ans, hands. split; [lia | exact Hs]. Qed.

(** A call made before a moment and not pending at it has completed by it. *)
Lemma called_and_over_completed (steps : Z -> Step) c who w :
  (exists m, m < w /\ calledBy steps c who m) ->
  ~ (exists m, m < w /\ begun steps c who m /\ ~ overBy steps who m w) ->
  exists from answer to, completedBy steps c who from answer to /\ from < w /\ to <= w.
Proof.
  intros (m & Hm & [Hbegun | (a & Hdone)]) Hnot.
  - destruct (classic (overBy steps who m w)) as [(k & a & hands & Hk & Hs) | Hpending].
    + exists m, a, (k + 1). split; [| lia].
      right. split; [exact Hbegun |]. exists hands. replace (k + 1 - 1) with k by lia. exact Hs.
    + exfalso. apply Hnot. exists m. split; [exact Hm | split; [exact Hbegun | exact Hpending]].
  - exists m, a, (m + 1). split; [left; split; [exact Hdone | reflexivity] | lia].
Qed.

(** ** A set known by its add and its remove *)

Lemma added_and_not_removed_is_in (steps : Z -> Step) (el : Z -> Thing -> Prop) (add rem : Thing -> Invocation) :
  (forall w, w < 0 -> steps w = Step_Rests) ->
  (forall x, (forall w who, calledBy steps (add x) who w -> exists a, doneAtOnce steps (add x) who w a) /\
             (forall w who, calledBy steps (rem x) who w -> exists a, doneAtOnce steps (rem x) who w a)) ->
  (forall x y from answer to, (exists who, completedBy steps (add x) who from answer to) ->
     el to y = (y = x \/ el from y)) ->
  (forall x y from answer to, (exists who, completedBy steps (rem x) who from answer to) ->
     el to y = (~ y = x /\ el from y)) ->
  (forall a b y, a < b /\ ~ (el a y = el b y) -> exists x,
     (exists a1 answer b1, (a <= a1 /\ b1 <= b) /\ exists who, completedBy steps (add x) who a1 answer b1) \/
     (exists a1 answer b1, (a <= a1 /\ b1 <= b) /\ exists who, completedBy steps (rem x) who a1 answer b1)) ->
  forall t w, (exists m, m < w /\ exists who, calledBy steps (add t) who m) ->
    ~ (exists m, m < w /\ exists who, calledBy steps (rem t) who m) -> el w t.
Proof.
  intros Hstart Hatomic Hadd Hrem Honly t w.
  destruct (Z_lt_le_dec w 0) as [Hneg | Hpos].
  { intros (m & Hm & who & Hc) _. exfalso.
    eapply (none_called_before_the_start steps); [exact Hstart | | exact Hc]; lia. }
  revert w Hpos. apply (natlike_ind (fun w => _ -> _ -> el w t)).
  { intros (m & Hm & who & Hc) _. exfalso.
    eapply (none_called_before_the_start steps); [exact Hstart | | exact Hc]; lia. }
  intros w Hw IH (m & Hm & who & Hc) Hno. unfold Z.succ in *.
  assert (m = w \/ m < w) as [-> | Hlt] by lia.
  - destruct (proj1 (Hatomic t) w who Hc) as (a & Hdone).
    rewrite (Hadd t t w a (w + 1)); [left; reflexivity |].
    exists who. left. split; [exact Hdone | reflexivity].
  - assert (el w t) as Hin.
    { apply IH; [exists m; split; [exact Hlt | exists who; exact Hc] |].
      intros (m' & Hm' & Hc'). apply Hno. exists m'. split; [lia | exact Hc']. }
    destruct (classic (el (w + 1) t)) as [H | Hout]; [exact H | exfalso].
    destruct (Honly w (w + 1) t) as (x & [Hx | Hx]).
    { split; [lia |]. intros E. apply Hout. rewrite <- E. exact Hin. }
    + destruct Hx as (a & answer & b & [Ha Hb] & who' & Hdone).
      destruct (atomic_completes_next steps _ who' a answer b (proj1 (Hatomic x)) Hdone) as [-> _].
      assert (a = w) as -> by lia. apply Hout.
      rewrite (Hadd x t w answer (w + 1)); [right; exact Hin | exists who'; exact Hdone].
    + destruct Hx as (a & answer & b & [Ha Hb] & who' & Hdone).
      destruct (atomic_completes_next steps _ who' a answer b (proj2 (Hatomic x)) Hdone) as [-> Hcalled].
      assert (a = w) as -> by lia.
      destruct (classic (t = x)) as [<- | Hne].
      * apply Hno. exists w. split; [lia | exists who'; exact Hcalled].
      * apply Hout. rewrite (Hrem x t w answer (w + 1)); [split; assumption | exists who'; exact Hdone].
Qed.

(** ** A run in which nothing happens

    It meets every statement that says what follows a call: what shows that statements can hold together. *)

Lemma nothing_begun_at_rest c who w : ~ begun (fun _ => Step_Rests) c who w.
Proof. intros (inside & H). discriminate. Qed.

Lemma nothing_called_at_rest c who w : ~ calledBy (fun _ => Step_Rests) c who w.
Proof. intros [(inside & H) | (a & inside & hands & H)]; discriminate. Qed.

Lemma nothing_completed_at_rest c who from a to : ~ completedBy (fun _ => Step_Rests) c who from a to.
Proof. intros [[(inside & hands & H) _] | [(inside & H) _]]; discriminate. Qed.

Lemma no_fork_at_rest heldIn t h w : ~ forkOf heldIn (fun _ => Step_Rests) t h w.
Proof. intros (m & _ & who & H). exact (nothing_called_at_rest _ _ _ H). Qed.

Lemma none_made_to_run_at_rest heldIn t h code w : ~ madeToRun heldIn (fun _ => Step_Rests) t h code w.
Proof. intros (c & m & [_ H] & _). exact (nothing_called_at_rest _ _ _ H). Qed.

Lemma none_closed_at_rest heldIn h w : ~ closed heldIn (fun _ => Step_Rests) h w.
Proof. intros [(m & _ & H) _]. exact (nothing_called_at_rest _ _ _ H). Qed.
