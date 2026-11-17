Require Export FrFlowGen.OxThreads.aForkThatEndedStaysOut.Spec.
Require Export Proofs.OxThreads.Lemmas.
From Stdlib Require Import String List ZArith Lia.

(** The function asked for the current thread, which is the thread and no null, and removed it by a call that is
    over: at a moment during that call the thread left the set. It does not come back. To enter the set again
    a call adding it would be in progress; such a call is made by a call of startThread, itself, for which a
    factory made the thread, before the thread is started; the thread has been started, having made a call, and
    only by that call of startThread, which starts a thread only once its add is over. *)
Lemma aForkThatEndedStaysOut_Proofs_complete : aForkThatEndedStaysOut_Obl_complete.
Proof.
  intros elements heldIn history [N C] Henters Hremoves Hobject Hout Hstarted Hover Honly Hnotstarted Hmaker Hmade
    Hbefore Hplain h r code t i ended e w b [[[Hcons Hfork] Hrun] Hew].
  set (S := heldIn "ox.internal.ThreadHerd threads"%string h).
  destruct (Hremoves h r code t i ended e (conj Hfork Hrun))
    as (a1 & b1 & Hcurrent & m & rr & n & [Hbm Hne] & Hremoved).
  assert (t <> Value_Null) as Hnotnull.
  { intros E. apply (Hobject a1 (Response_Returned t) b1); [exists t; exact Hcurrent | rewrite E; reflexivity]. }
  destruct (Hout S t Hnotnull m rr n (ex_intro _ t Hremoved)) as (q & [Hmq Hqn] & Heffect).
  assert (~ elements S (q + 1) t) as Hgone.
  { rewrite (Heffect t). intros [Hne' _]. apply Hne'. reflexivity. }
  pose proof (completed_after C Hcurrent) as Hab.
  assert (forall k, q + 1 <= k -> ~ elements S k t) as Hstays.
  { apply (from_a_moment_on (fun k => ~ elements S k t) (q + 1) Hgone).
    intros k Hk Hnot Hin.
    assert (exists c2 w2, w2 <= k /\ calledBy history (Invocation_mk
        "java.util.concurrent.ConcurrentHashMap$.KeySetView add java.lang.Object:scala.Boolean"%string [S; t]) c2 w2 /\
      (w2 < k -> begun history (Invocation_mk
        "java.util.concurrent.ConcurrentHashMap$.KeySetView add java.lang.Object:scala.Boolean"%string [S; t]) c2 w2 /\
        ~ overBy history c2 w2 k)) as (c2 & w2 & Hw2 & Hcalled2 & Hpending2).
    { destruct (Henters S t k (conj (conj (Hplain h b Hcons) Hnot) Hin)) as [[who Hc] | (m2 & Hm2 & who & Hb & Hno)].
      - exists who, k. split; [lia | split; [exact Hc | intros; lia]].
      - exists who, m2. split; [lia | split; [left; exact Hb | intros _; split; assumption]]. }
    destruct (Honly h t c2 w2 b (conj Hcons Hcalled2)) as (code2 & from2 & Hstart2 & Hadds2).
    pose proof (Hmade h code2 c2 t from2 w2 (conj Hstart2 Hadds2)) as Hfor.
    destruct Hfor as (f & r0 & a0 & done & [Hdone Hnew] & Hnewdone).
    destruct (Hstarted f r0 t a0 done _ a1
      (conj (ex_intro _ c2 Hnewdone) (completed_was_called _ _ _ _ _ _ Hcurrent))) as (ms & Hms & other & Hstart).
    pose proof (Hmaker h code2 c2 t from2 w2 ms other
      (conj (conj Hstart2 (Hmade h code2 c2 t from2 w2 (conj Hstart2 Hadds2))) Hstart)) as Hstarts.
    pose proof (Hbefore h code2 c2 t from2 w2 ms t (conj (conj Hstart2 Hadds2) Hstarts)) as Hlt.
    destruct (Hpending2 ltac:(lia)) as [Hb2 Hno2].
    apply (Hover h code2 c2 t from2 w2 ms t (conj (conj Hstart2 Hadds2) Hstarts)).
    split; [exact Hlt | split; [exact Hb2 |]].
    intros Hov. apply Hno2. exact (over_later history c2 w2 ms k ltac:(lia) Hov). }
  apply (Hstays w). lia.
Qed.

(** What it is from can hold: an execution in which nothing happens, of sets that hold nothing, meets each. *)
Lemma aForkThatEndedStaysOut_Proofs_feasible : aForkThatEndedStaysOut_Obl_feasible.
Proof.
  exists (fun _ _ _ => False), (fun _ x => x), (fun _ => Event_Stutter).
  split; [exact rest_runs |].
  split.
  { intros s x w [_ H]. destruct H. }
  split.
  { intros h r code t i ended e [_ H]. destruct (nothing_completed_at_rest _ _ _ _ _ H). }
  split.
  { intros from response to [who H]. destruct (nothing_completed_at_rest _ _ _ _ _ H). }
  split.
  { intros s x _ from response to [who H]. destruct (nothing_completed_at_rest _ _ _ _ _ H). }
  split.
  { intros f r t a b made w [[who H] _]. destruct (nothing_completed_at_rest _ _ _ _ _ H). }
  split.
  { intros h code c t from w m started [[H _] _]. destruct (nothing_called_at_rest _ _ _ H). }
  split.
  { intros h t c w b [_ H]. destruct (nothing_called_at_rest _ _ _ H). }
  split.
  { intros h t c w b [_ H]. destruct (nothing_called_at_rest _ _ _ H). }
  split.
  { intros h code c t from b m other [[H _] _]. destruct (nothing_called_at_rest _ _ _ H). }
  split.
  { intros h code c t from w [H _]. destruct (nothing_called_at_rest _ _ _ H). }
  split.
  { intros h code c t from w m started [[H _] _]. destruct (nothing_called_at_rest _ _ _ H). }
  intros h w Hready. destruct (nothing_ready_at_rest _ _ _ Hready).
Qed.
