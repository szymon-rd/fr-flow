Require Export FrFlowGen.OxThreads.Domain.
Require Import FrFlow.Code.Walk.

(** An execution in which nothing happens is one of the code. *)
Lemma rest_runs : Code_runs (fun _ => Event_Stutter).
Proof. apply nothing_runs. Qed.

(** ** The moments from one on *)

Lemma from_a_moment_on (P : Z -> Prop) (m : Z) :
  P m -> (forall k, m <= k -> P k -> P (k + 1)) -> forall k, m <= k -> P k.
Proof.
  intros Hm Hstep k Hk. replace k with (m + (k - m)) by lia.
  apply (natlike_ind (fun d => P (m + d))); [replace (m + 0) with m by lia; exact Hm | | lia].
  intros d Hd IH. replace (m + Z.succ d) with (m + d + 1) by lia. apply Hstep; [lia | exact IH].
Qed.

(** ** One step from each moment *)

Lemma none_called_before_the_start (history : Z -> Event) c who m :
  (forall w, w < 0 -> history w = Event_Stutter) -> m < 0 -> ~ calledBy history c who m.
Proof.
  intros Hstart Hm Hc. assert (history m = Event_Stutter) as E by (apply Hstart; exact Hm).
  destruct Hc as [(inside & Hc) | (a & inside & spawns & Hc)]; rewrite E in Hc; discriminate.
Qed.

(** What is called at a moment is one call, by one actor. *)
Lemma one_call_at_a_moment (history : Z -> Event) c1 c2 who1 who2 w :
  calledBy history c1 who1 w -> calledBy history c2 who2 w -> c1 = c2 /\ who1 = who2.
Proof.
  intros [(i1 & H1) | (a1 & i1 & h1 & H1)] [(i2 & H2) | (a2 & i2 & h2 & H2)]; rewrite H1 in H2;
    try discriminate; injection H2; intros; subst; split; reflexivity.
Qed.

Lemma begun_is_called (history : Z -> Event) c who w : begun history c who w -> calledBy history c who w.
Proof. intros H. left. exact H. Qed.

Lemma completed_was_called (history : Z -> Event) c who from response to :
  completedBy history c who from response to -> calledBy history c who from.
Proof. intros [[Hdone _] | [Hbegun _]]; [right; exists response; exact Hdone | left; exact Hbegun]. Qed.

(** A completed call of what is atomic was made one moment before. *)
Lemma atomic_completes_next (history : Z -> Event) c who from response to :
  (forall w who, calledBy history c who w -> exists a, doneAtOnce history c who w a) ->
  completedBy history c who from response to -> to = from + 1 /\ calledBy history c who from.
Proof.
  intros Hatomic [[Hdone ->] | [Hbegun _]].
  - split; [reflexivity | right; exists response; exact Hdone].
  - destruct (Hatomic from who (or_introl Hbegun)) as (a & inside & spawns & Hdoes).
    destruct Hbegun as (inside' & Hmakes). rewrite Hmakes in Hdoes. discriminate.
Qed.

Lemma over_later (history : Z -> Event) who from a b : a <= b -> overBy history who from a -> overBy history who from b.
Proof. intros Hab (k & ans & spawns & Hk & Hs). exists k, ans, spawns. split; [lia | exact Hs]. Qed.

(** A call made before a moment and not pending at it has completed by it. *)
Lemma called_and_over_completed (history : Z -> Event) c who w :
  (exists m, m < w /\ calledBy history c who m) ->
  ~ (exists m, m < w /\ begun history c who m /\ ~ overBy history who m w) ->
  exists from response to, completedBy history c who from response to /\ from < w /\ to <= w.
Proof.
  intros (m & Hm & [Hbegun | (a & Hdone)]) Hnot.
  - destruct (classic (overBy history who m w)) as [(k & a & spawns & Hk & Hs) | Hpending].
    + exists m, a, (k + 1). split; [| lia].
      right. split; [exact Hbegun |]. exists spawns. replace (k + 1 - 1) with k by lia. exact Hs.
    + exfalso. apply Hnot. exists m. split; [exact Hm | split; [exact Hbegun | exact Hpending]].
  - exists m, a, (m + 1). split; [left; split; [exact Hdone | reflexivity] | lia].
Qed.

(** ** A set known by its add and its remove *)

Lemma added_and_not_removed_is_in (history : Z -> Event) (el : Z -> Value -> Prop) (add rem : Value -> Invocation) :
  (forall w, w < 0 -> history w = Event_Stutter) ->
  (forall x, (forall w who, calledBy history (add x) who w -> exists a, doneAtOnce history (add x) who w a) /\
             (forall w who, calledBy history (rem x) who w -> exists a, doneAtOnce history (rem x) who w a)) ->
  (forall x y from response to, (exists who, completedBy history (add x) who from response to) ->
     el to y = (y = x \/ el from y)) ->
  (forall x y from response to, (exists who, completedBy history (rem x) who from response to) ->
     el to y = (~ y = x /\ el from y)) ->
  (forall a b y, a < b /\ ~ (el a y = el b y) -> exists x,
     (exists a1 response b1, (a <= a1 /\ b1 <= b) /\ exists who, completedBy history (add x) who a1 response b1) \/
     (exists a1 response b1, (a <= a1 /\ b1 <= b) /\ exists who, completedBy history (rem x) who a1 response b1)) ->
  forall t w, (exists m, m < w /\ exists who, calledBy history (add t) who m) ->
    ~ (exists m, m < w /\ exists who, calledBy history (rem t) who m) -> el w t.
Proof.
  intros Hstart Hatomic Hadd Hrem Honly t w.
  destruct (Z_lt_le_dec w 0) as [Hneg | Hpos].
  { intros (m & Hm & who & Hc) _. exfalso.
    eapply (none_called_before_the_start history); [exact Hstart | | exact Hc]; lia. }
  revert w Hpos. apply (natlike_ind (fun w => _ -> _ -> el w t)).
  { intros (m & Hm & who & Hc) _. exfalso.
    eapply (none_called_before_the_start history); [exact Hstart | | exact Hc]; lia. }
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
    + destruct Hx as (a & response & b & [Ha Hb] & who' & Hdone).
      destruct (atomic_completes_next history _ who' a response b (proj1 (Hatomic x)) Hdone) as [-> _].
      assert (a = w) as -> by lia. apply Hout.
      rewrite (Hadd x t w response (w + 1)); [right; exact Hin | exists who'; exact Hdone].
    + destruct Hx as (a & response & b & [Ha Hb] & who' & Hdone).
      destruct (atomic_completes_next history _ who' a response b (proj2 (Hatomic x)) Hdone) as [-> Hcalled].
      assert (a = w) as -> by lia.
      destruct (classic (t = x)) as [<- | Hne].
      * apply Hno. exists w. split; [lia | exists who'; exact Hcalled].
      * apply Hout. rewrite (Hrem x t w response (w + 1)); [split; assumption | exists who'; exact Hdone].
Qed.

(** ** A run in which nothing happens

    It meets every statement that says what follows a call: what shows that statements can hold together. *)

Lemma nothing_begun_at_rest c who w : ~ begun (fun _ => Event_Stutter) c who w.
Proof. intros (inside & H). discriminate. Qed.

Lemma nothing_called_at_rest c who w : ~ calledBy (fun _ => Event_Stutter) c who w.
Proof. intros [(inside & H) | (a & inside & spawns & H)]; discriminate. Qed.

Lemma nothing_completed_at_rest c who from a to : ~ completedBy (fun _ => Event_Stutter) c who from a to.
Proof. intros [[(inside & spawns & H) _] | [(inside & H) _]]; discriminate. Qed.

Lemma no_fork_at_rest heldIn t h w : ~ forkOf heldIn (fun _ => Event_Stutter) t h w.
Proof. intros (m & _ & who & H). exact (nothing_called_at_rest _ _ _ H). Qed.

Lemma none_made_to_run_at_rest heldIn t h code w : ~ madeToRun heldIn (fun _ => Event_Stutter) t h code w.
Proof. intros (c & m & [_ H] & _). exact (nothing_called_at_rest _ _ _ H). Qed.

Lemma none_closed_at_rest heldIn h w : ~ closed heldIn (fun _ => Event_Stutter) h w.
Proof. intros [(m & _ & H) _]. exact (nothing_called_at_rest _ _ _ H). Qed.
