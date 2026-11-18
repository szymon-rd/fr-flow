Require Export FrFlowGen.OxThreads.Domain.
Require Import FrFlow.Jvm.Prog FrFlow.Jvm.Machine.
Require Import FrFlow.Scala.Tree FrFlow.Scala.Table FrFlow.Scala.Value FrFlow.Scala.Meaning.
Require Import FrFlow.Code.Outside FrFlow.Code.Conforms FrFlow.Rules.Walk FrFlow.Rules.Logic FrFlow.Rules.Live.

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
  readAs history h L.ThreadHerd_herdOwner (heldIn L.ThreadHerd_herdOwner h) ->
  (forall c from response to, completedBy history
    (Invocation_mk L.Thread_currentThread []) c from response to ->
    response = Response_Returned c) ->
  names N h (vref "ox.internal.ThreadHerd" r) ->
  history w1 = Event_Invoke (heldIn L.ThreadHerd_herdOwner h) inside
    (Invocation_mk L.ThreadHerd_assertOnOwnerThread [h]) ->
  forall w, direct (heldIn L.ThreadHerd_herdOwner h) w1 (history w) -> forall y sp,
    history w = Event_Respond (heldIn L.ThreadHerd_herdOwner h) w1 (Response_Threw y) sp -> False.
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
    (Invocation_mk L.ThreadHerd_isOwnerOrHerdThread [h; t]) ->
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

(** A herd that is ready by a moment is ready by every later one. *)
Lemma herd_constructed_later {heldIn : string -> Value -> Value} (history : Z -> Event) h a b : a <= b ->
  ready heldIn history h a -> ready heldIn history h b.
Proof.
  intros Hab [(x & by_ & from & to & Hto & H) | (su & em & pa & lo & s & from & to & [[Hto H] E])].
  - left. exists x, by_, from, to. split; [lia | exact H].
  - right. exists su, em, pa, lo, s, from, to. split; [split; [lia | exact H] | exact E].
Qed.

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

(** Of an object and a call that itself made it and has responded, having written each field of the object it
    marked. A field that only the maker of the object marks and writes, inside the call that makes it, is marked
    and written by that call alone: so it is not being written once the call has responded, nor marked or written
    again. *)
Lemma made_then_settled (history : Z -> Event) (N : naming) (h : Value) (cls : string) (c : Value)
    (from k : Z) r sp (field : string) :
  conforms Code_files Code_table Code_classes N history ->
  (exists m hs, history m = Event_Make c (Some from) h cls hs) ->
  history k = Event_Respond c from r sp ->
  (forall w, k < w -> ~ direct c from (history w)) ->
  (forall m f, m < k -> history m = Event_Mark c (Some from) h f ->
     exists k' v, m < k' /\ k' < k /\ history k' = Event_Write c (Some from) h f v) ->
  (forall by_ inside w, assigns history h field by_ inside w ->
     exists m cls hs, m < w /\ history m = Event_Make by_ inside h cls hs) ->
  forall by_ inside later, k < later ->
    ~ Def_writing.writing history h field by_ later /\ ~ assigns history h field by_ inside later.
Proof.
  intros C (m0 & hs0 & Hmade) Hk Hover Hmarks Hassigned.
  assert (forall by_ inside w, assigns history h field by_ inside w -> by_ = c /\ inside = Some from) as Hwho.
  { intros by_ inside w Ha. destruct (Hassigned by_ inside w Ha) as (m & cls' & hs & _ & Hm).
    pose proof (made_at_one C Hm Hmade) as ->. rewrite Hmade in Hm. injection Hm; intros; subst.
    split; reflexivity. }
  intros by_ inside later Hlater. split.
  - intros (m & ins & [Hm Hmark] & Hnone).
    destruct (Hwho by_ ins m (or_introl Hmark)) as [-> ->].
    assert (m < k) as Hmk.
    { destruct (Z_lt_le_dec m k) as [Hlt | Hge]; [exact Hlt | exfalso].
      assert (m = k \/ k < m) as [-> | Hgt] by lia.
      - rewrite Hk in Hmark. discriminate Hmark.
      - apply (Hover m Hgt). rewrite Hmark. cbn. auto. }
    destruct (Hmarks m field Hmk Hmark) as (k' & v & Hk1 & Hk2 & Hwrite).
    assert (m < k' /\ k' < later) as Hbetween by lia.
    exact (Hnone k' (Some from) v Hbetween Hwrite).
  - intros Ha. destruct (Hwho by_ inside later Ha) as [-> ->].
    apply (Hover later Hlater). destruct Ha as [Ha | [v Ha]]; rewrite Ha; cbn; auto.
Qed.

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

(** Finitely many moments in a window: what comes to hold of each, and then stays, holds of all from a moment. *)
Lemma all_over_a_window (Q : Z -> Z -> Prop) (lo : Z) :
  (forall s e e', Q s e -> e <= e' -> Q s e') -> (forall s, exists e, Q s e) ->
  forall n : nat, exists E, forall s, lo <= s < lo + Z.of_nat n -> Q s E.
Proof.
  intros Hstays Hcomes. induction n as [| n [E IH]].
  - exists 0. intros s Hs. lia.
  - destruct (Hcomes (lo + Z.of_nat n)) as [e He]. exists (Z.max E e). intros s Hs.
    destruct (Z.eq_dec s (lo + Z.of_nat n)) as [-> | Hne].
    + apply (Hstays _ e); [exact He | lia].
    + apply (Hstays s E); [apply IH; lia | lia].
Qed.
