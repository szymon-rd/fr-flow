Require Export FrFlowGen.OxThreads.Domain.
Require Import FrFlow.Threads.Prog FrFlow.Jvm.Machine.
Require Import FrFlow.Scala.Tree FrFlow.Scala.Table FrFlow.Scala.Value FrFlow.Scala.Meaning.
Require Import FrFlow.Code.Outside FrFlow.Code.Conforms FrFlow.Code.Walk FrFlow.Code.Logic.

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

(** What was made before a moment was made before every later one. *)
Lemma made_later (history : Z -> Event) h cls a b : a <= b -> madeBefore history h cls a -> madeBefore history h cls b.
Proof. intros Hab (m & by_ & ins & hs & Hm & H). exists m, by_, ins, hs. split; [lia | exact H]. Qed.

(** A call completes after it is made. *)
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
    while one of those is pending. *)
Lemma called_under (history : Z -> Event) (allowed : Invocation -> Prop) who outer from inner w :
  oneAtATime history who ->
  (forall made k, itselfMakes history made who from k -> allowed made) ->
  (from < w /\ begun history outer who from) /\ ~ overBy history who from w -> calledBy history inner who w ->
  allowed inner \/ exists between m, allowed between /\
    (m < w /\ begun history between who m) /\ ~ overBy history who m w.
Proof.
  intros Hone Hall [[Hlt Hbegun] Hnot] Hcalled.
  destruct (Hone outer from inner w (conj (conj (conj Hlt Hbegun) Hnot) Hcalled))
    as [Hit | (between & m & [[[Hfm Hmw] Hat] Hpending])].
  - left. exact (Hall inner w Hit).
  - right. exists between, m. split; [apply (Hall between m); left; exact Hat |].
    split; [split; [exact Hmw | exists (Some from); exact Hat] | exact Hpending].
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
