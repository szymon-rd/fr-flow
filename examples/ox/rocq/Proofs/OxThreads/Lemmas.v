Require Export FrFlowGen.OxThreads.Domain.
Require Import FrFlow.Threads.Prog FrFlow.Jvm.Machine.
Require Import FrFlow.Scala.Tree FrFlow.Scala.Table FrFlow.Scala.Value FrFlow.Scala.Meaning.
Require Import FrFlow.Code.Outside FrFlow.Code.Conforms FrFlow.Code.Walk FrFlow.Code.Logic FrFlow.Code.Live.

(** An execution in which nothing happens is one of the code. *)
Lemma rest_runs : Code_runs (fun _ => Event_Stutter).
Proof. apply nothing_runs. Qed.

(** ** Calls of the herd's methods in an execution of the code *)

(** A call of a method of the code, on an object the execution says was made: the object is one of the code, and
    the call is no event made and responded to at once. *)
Lemma method_begun {history : Z -> Event} {N} s {cls d h ys c from} :
  conforms Code_files Code_table Code_classes N history -> madeBefore history h cls from ->
  impl Code_table cls s = Some d -> calledBy history (Invocation_mk (label_of s) (h :: ys)) c from ->
  exists r inside, names N h (vref cls r) /\
    history from = Event_Invoke c inside (Invocation_mk (label_of s) (h :: ys)).
Proof.
  intros C (m & b & ins & hs & _ & Hmk) Hd Hcalled. destruct (made_named C Hmk) as [r Hh].
  destruct Hcalled as [[inside Hcall] | (a & inside & spawns & Hat)]; [exists r, inside; auto |].
  exfalso. exact (method_not_atomic C s Hat Hh Hd).
Qed.

(** A call made inside a call and responded to: what the model's words say of it. *)
Lemma done_made {history : Z -> Event} {c from m ys w1 r w2} :
  done_inside history c from m ys w1 r w2 -> itselfMakes history (Invocation_mk m ys) c from w1.
Proof. intros [(sp & H & _) | (H & _)]; [right; eauto | left; exact H]. Qed.

Lemma done_completed {history : Z -> Event} {c from m ys w1 r w2} :
  done_inside history c from m ys w1 r w2 -> completedBy history (Invocation_mk m ys) c w1 r w2.
Proof.
  intros [(sp & H & ->) | (H & _ & sp & Hr)].
  - left. split; [exists (Some from), sp; exact H | reflexivity].
  - right. split; [exists (Some from); exact H | exists sp; exact Hr].
Qed.

Lemma done_by_someone {history : Z -> Event} {c from m ys w1 r w2} :
  done_inside history c from m ys w1 r w2 -> exists who, completedBy history (Invocation_mk m ys) who w1 r w2.
Proof. intros H. exists c. exact (done_completed H). Qed.

(** Proven of `ThreadHerd.assertOnOwnerThread`'s tree: it compares `Thread.currentThread()` with the herd's
    owner and throws if they differ, so a call of it by the owner does not throw. *)
Lemma assertOnOwnerThread_returns {heldIn} {history : Z -> Event} {N h r inside w1} :
  conforms Code_files Code_table Code_classes N history ->
  readAs history h "ox.internal.ThreadHerd herdOwner" (heldIn "ox.internal.ThreadHerd herdOwner" h) ->
  (forall c from response to, completedBy history
    (Invocation_mk "java.lang.Thread$ currentThread :java.lang.Thread" []) c from response to ->
    response = Response_Returned c) ->
  names N h (vref "ox.internal.ThreadHerd" r) ->
  history w1 = Event_Invoke (heldIn "ox.internal.ThreadHerd herdOwner" h) inside
    (Invocation_mk "ox.internal.ThreadHerd assertOnOwnerThread :scala.Unit" [h]) ->
  forall w, direct (heldIn "ox.internal.ThreadHerd herdOwner" h) w1 (history w) -> forall y sp,
    history w = Event_Respond (heldIn "ox.internal.ThreadHerd herdOwner" h) w1 (Response_Threw y) sp -> False.
Proof.
  intros C Howner Hcurrent Hh Hcall.
  refine (method_meets _ C (Member "ox.internal.ThreadHerd" "assertOnOwnerThread" ":scala.Unit") Hcall Hh
    eq_refl _).
  intros args k Hargs _. apply vals_none in Hargs as ->.
  (* Thread.currentThread(): the owner *)
  step. intros wc ys _ _ Hys Hmk. split; [miss |]. intros wd a x _ Hcur Hgives Hty.
  apply args_none in Hys as ->. rewrite (Hcurrent _ _ _ _ (done_completed Hcur)) in Hgives.
  destruct x as [e | current]; [contradiction |].
  (* the herd's owner, read: the same thread *)
  step. intros wr v y _ _ Hy Htyv Hread. split; [miss |]. apply Howner in Hread. subst y.
  pose proof (names_one N _ _ _ Hy Hgives) as ->.
  (* so nothing is thrown *)
  pass.
Qed.

(** Proven of `ThreadHerd.isOwnerOrHerdThread`'s tree: what a call of it returns is a truth value. *)
Lemma isOwnerOrHerdThread_returns {history : Z -> Event} {N h r t c inside w1} :
  conforms Code_files Code_table Code_classes N history ->
  names N h (vref "ox.internal.ThreadHerd" r) ->
  history w1 = Event_Invoke c inside
    (Invocation_mk "ox.internal.ThreadHerd isOwnerOrHerdThread java.lang.Thread:scala.Boolean" [h; t]) ->
  forall w, direct c w1 (history w) -> forall resp sp x,
    history w = Event_Respond c w1 resp sp -> gives N resp (inr x) -> exists b, x = VBool b.
Proof.
  intros C Hh Hcall.
  refine (method_meets _ C (Member "ox.internal.ThreadHerd" "isOwnerOrHerdThread" "java.lang.Thread:scala.Boolean")
    Hcall Hh eq_refl _).
  intros args k Hargs Hpassed. apply vals_one in Hargs as (vt & -> & _).
  inversion Hpassed as [| pt vt' pst vst Hthread _]; subst. typed Hthread.
  (* the owner is read: it is the thread, or the set is read and asked *)
  pass. meets_head; [| pass; step; intros wask ys _ _ Hys Hmk1; (split; [miss |]);
    intros wasked rask xask _ _ _ Hretask; meets_head].
  all: apply meets_ret; intros rr _ _ Hrr Hgives resp sp x Hresp Hgx; rewrite Hrr in Hresp;
    injection Hresp as <- _; destruct rr; cbn in Hgives, Hgx; try contradiction; eexists;
    exact (names_one N _ _ _ Hgx Hgives).
Qed.

(** A herd that its constructor has returned by a moment, it has returned by every later one. *)
Lemma herd_constructed_later (history : Z -> Event) h a b : a <= b ->
  (exists x by_ from to, to <= a /\ completedBy history (Invocation_mk
    "ox.internal.ThreadHerd <init> java.util.concurrent.ThreadFactory:ox.internal.ThreadHerd"%string [x])
    by_ from (Response_Returned h) to) ->
  exists x by_ from to, to <= b /\ completedBy history (Invocation_mk
    "ox.internal.ThreadHerd <init> java.util.concurrent.ThreadFactory:ox.internal.ThreadHerd"%string [x])
    by_ from (Response_Returned h) to.
Proof. intros Hab (x & by_ & from & to & Hto & H). exists x, by_, from, to. split; [lia | exact H]. Qed.

Lemma completed_after {history : Z -> Event} {N c who from r to} :
  conforms Code_files Code_table Code_classes N history -> completedBy history c who from r to -> from < to.
Proof. intros C [[_ ->] | [_ (sp & Hr)]]; [lia |]. pose proof (responded_after C Hr). lia. Qed.

(** A call that completes after a moment and was made before it is pending at it: it is responded to once. *)
Lemma still_pending {history : Z -> Event} {N c who from r to} m :
  conforms Code_files Code_table Code_classes N history -> completedBy history c who from r to -> from < m -> m < to ->
  from < m /\ begun history c who from /\ ~ overBy history who from m.
Proof.
  intros C [[_ ->] | [Hb (sp & Hr)]] Hfm Hmt; [lia |].
  split; [exact Hfm | split; [exact Hb |]]. intros (k & a & sp' & Hk & Hk').
  pose proof (responded_once C Hk' Hr). lia.
Qed.

(** ** The moments from one on *)

Lemma from_a_moment_on (P : Z -> Prop) (m : Z) :
  P m -> (forall k, m <= k -> P k -> P (k + 1)) -> forall k, m <= k -> P k.
Proof.
  intros Hm Hstep k Hk. replace k with (m + (k - m)) by lia.
  apply (natlike_ind (fun d => P (m + d))); [replace (m + 0) with m by lia; exact Hm | | lia].
  intros d Hd IH. replace (m + Z.succ d) with (m + d + 1) by lia. apply Hstep; [lia | exact IH].
Qed.

(** ** One step from each moment *)

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

(** A response that gives unit is the return of unit. *)
Lemma returned_unit (N : naming) (r : Response) : gives N r (inr VUnit) -> r = Response_Returned Value_Unit_.
Proof. destruct r as [y | y]; [| contradiction]. intros H. f_equal. exact (one_name N _ _ _ H (of_unit N)). Qed.

(** What is thrown, where the response says it is an InterruptedException of the JDK. *)
Lemma threw_interruption (N : naming) (e : exn) :
  gives N (Response_Threw (Value_Thrown "java.lang.InterruptedException")) (inl e) -> e = InterruptedException.
Proof.
  intros H. pose proof (names_one N _ _ _ H (of_thrown N _)) as E.
  destruct e; cbn in E; try discriminate E; try reflexivity; injection E as E; discriminate E.
Qed.

(** ** One thing at a time *)

(** What an actor calls while a call of its own is pending is among what that call itself calls, or is called
    while one of those, made later, is pending. *)
Lemma called_under_later (history : Z -> Event) (allowed : Invocation -> Prop) who outer from inner w :
  oneAtATime history who ->
  (forall made k, itselfMakes history made who from k -> allowed made) ->
  (from < w /\ begun history outer who from) /\ ~ overBy history who from w -> calledBy history inner who w ->
  allowed inner \/ exists between m, from < m /\ allowed between /\
    (m < w /\ begun history between who m) /\ ~ overBy history who m w.
Proof.
  intros Hone Hall [[Hlt Hbegun] Hnot] Hcalled.
  assert (exists inside, does history who inside w /\
    (inside = Some from -> itselfMakes history inner who from w)) as (inside & Hdoes & Hthen).
  { destruct Hcalled as [(inside & H) | (a & inside & sp & H)]; exists inside;
      (split; [unfold does; rewrite H; split; reflexivity |]); intros ->; [left | right; exists a, sp]; exact H. }
  destruct (Hone outer from inside w (conj (conj (conj Hlt Hbegun) Hnot) Hdoes))
    as [E | (between & m & [[[Hfm Hmw] Hat] Hpending])].
  - left. exact (Hall inner w (Hthen E)).
  - right. exists between, m. split; [exact Hfm |]. split; [apply (Hall between m); left; exact Hat |].
    split; [split; [exact Hmw | exists (Some from); exact Hat] | exact Hpending].
Qed.

Lemma called_under (history : Z -> Event) (allowed : Invocation -> Prop) who outer from inner w :
  oneAtATime history who ->
  (forall made k, itselfMakes history made who from k -> allowed made) ->
  (from < w /\ begun history outer who from) /\ ~ overBy history who from w -> calledBy history inner who w ->
  allowed inner \/ exists between m, allowed between /\
    (m < w /\ begun history between who m) /\ ~ overBy history who m w.
Proof.
  intros Hone Hall Hpending Hcalled.
  destruct (called_under_later history allowed who outer from inner w Hone Hall Hpending Hcalled)
    as [H | (between & m & _ & H)]; [left; exact H | right; exists between, m; exact H].
Qed.

(** What an actor writes while a call of its own is pending, and every call that call itself made is over, the
    call writes itself. *)
Lemma written_itself (history : Z -> Event) who outer from inside on field value w :
  oneAtATime history who -> from < w -> begun history outer who from -> ~ overBy history who from w ->
  history w = Event_Write who inside on field value ->
  (forall between m, from < m -> m < w -> history m = Event_Invoke who (Some from) between ->
    overBy history who m w) ->
  inside = Some from.
Proof.
  intros Hone Hlt Hbegun Hnot Hwrite Hover.
  destruct (Hone outer from inside w) as [E | (between & m & [[[Hfm Hmw] Hat] Hpending])]; [| exact E |].
  - split; [split; [split; assumption | exact Hnot] |]. unfold does. rewrite Hwrite. split; reflexivity.
  - destruct (Hpending (Hover between m Hfm Hmw Hat)).
Qed.

(** ** A run in which nothing happens

    It meets every statement that says what follows a call: what shows that statements can hold together. *)

Lemma nothing_begun_at_rest c who w : ~ begun (fun _ => Event_Stutter) c who w.
Proof. intros (inside & H). discriminate. Qed.

Lemma nothing_called_at_rest c who w : ~ calledBy (fun _ => Event_Stutter) c who w.
Proof. intros [(inside & H) | (a & inside & spawns & H)]; discriminate. Qed.

Lemma nothing_called_on_at_rest on method w : ~ calledOn (fun _ => Event_Stutter) on method w.
Proof. intros (rest & by_ & H). exact (nothing_called_at_rest _ _ _ H). Qed.

Lemma nothing_completed_at_rest c who from a to : ~ completedBy (fun _ => Event_Stutter) c who from a to.
Proof. intros [[(inside & spawns & H) _] | [(inside & H) _]]; discriminate. Qed.

Lemma no_fork_at_rest heldIn t h w : ~ forkOf heldIn (fun _ => Event_Stutter) t h w.
Proof. intros (from & value & to & _ & who & H). exact (nothing_completed_at_rest _ _ _ _ _ H). Qed.

Lemma none_made_to_run_at_rest heldIn t h code w : ~ madeToRun heldIn (fun _ => Event_Stutter) t h code w.
Proof. intros (c & from & added & to & [_ H] & _). exact (nothing_completed_at_rest _ _ _ _ _ H). Qed.

(** ** What happens in time *)

(** An event of a call's own, as the model's word has it. *)
Lemma acts_direct (history : Z -> Event) who from w : actsItself history who from w -> direct who from (history w).
Proof.
  intros [H | (r & sp & E)]; [| rewrite E; cbn; auto].
  unfold does in H. destruct (history w); cbn; try contradiction; exact H.
Qed.

(** A call that proceeds, as the walk takes it: pending and waiting for no call it made, it makes its next
    event. *)
Lemma proceeds_moves (history : Z -> Event) who from : proceedsFrom history who from -> moves history who from.
Proof.
  intros H w Hw Hp Ha. destruct (H w) as (later & Hl & Hact).
  - split; [split; [exact Hw |] |].
    + intros (k & r & sp & Hk & E). exact (Hp k r sp Hk E).
    + intros (m & inner & [Hm E] & Hnot).
      destruct (Ha m inner Hm ltac:(discriminate) E) as (k & r & sp & Hk & Ek).
      apply Hnot. exists k, r, sp. split; assumption.
  - exists later. split; [exact Hl | exact (acts_direct _ _ _ _ Hact)].
Qed.

(** A call that is over was responded to. *)
Lemma over_responded (history : Z -> Event) who i w1 to : overBy history who w1 to -> responded history who i w1.
Proof. intros (k & r & sp & _ & E). left. exists k, r, sp. exact E. Qed.

(** What a call inside another gave, where the execution says how it completed: the one response. *)
Lemma done_gave {history : Z -> Event} {N c from m ys w1 r w2} who r' w2' :
  conforms Code_files Code_table Code_classes N history ->
  done_inside history c from m ys w1 r w2 -> completedBy history (Invocation_mk m ys) who w1 r' w2' -> r = r'.
Proof.
  intros C [(sp & E & _) | (E & _ & sp & Er)] [[(ins & sp' & E') _] | [[ins E'] [sp' Er']]].
  - rewrite E in E'. injection E'. intros. subst. reflexivity.
  - rewrite E in E'. discriminate E'.
  - rewrite E in E'. discriminate E'.
  - rewrite E in E'. injection E' as <- _.
    pose proof (responded_once C Er Er') as Ew. rewrite Ew in Er. rewrite Er in Er'. injection Er'. auto.
Qed.

(** Finitely many moments in a window: what happens at most once for each has a moment after all of it. *)
Lemma bounded_over_a_window (P : Z -> Z -> Prop) (lo : Z) :
  (forall s w w', P s w -> P s w' -> w = w') ->
  forall n : nat, exists B, forall s w, lo <= s < lo + Z.of_nat n -> P s w -> w < B.
Proof.
  intros Hone. induction n as [| n [B IH]].
  - exists 0. intros s w Hs. lia.
  - destruct (Classical_Prop.classic (exists w, P (lo + Z.of_nat n) w)) as [[w0 H0] | Hnone].
    + exists (Z.max B (w0 + 1)). intros s w Hs Hp. destruct (Z.eq_dec s (lo + Z.of_nat n)) as [-> | Hne].
      * rewrite (Hone _ _ _ Hp H0). lia.
      * pose proof (IH s w ltac:(lia) Hp). lia.
    + exists B. intros s w Hs Hp. destruct (Z.eq_dec s (lo + Z.of_nat n)) as [-> | Hne].
      * exfalso. apply Hnone. exists w. exact Hp.
      * exact (IH s w ltac:(lia) Hp).
Qed.
