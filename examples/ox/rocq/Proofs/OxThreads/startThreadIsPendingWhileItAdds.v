Require Export FrFlowGen.OxThreads.startThreadIsPendingWhileItAdds.Spec.
Require Export Proofs.OxThreads.Lemmas.
From Stdlib Require Import String List ZArith Lia.
Require Import FrFlow.Threads.Prog FrFlow.Jvm.Machine.
Require Import FrFlow.Scala.Tree FrFlow.Scala.Table FrFlow.Scala.Value FrFlow.Scala.Meaning.
Require Import FrFlow.Code.Outside FrFlow.Code.Conforms FrFlow.Code.Walk FrFlow.Code.Logic.

(** Proven of `ThreadHerd.startThread`'s tree: its response comes after the response to the add it made. So
    while that add is pending, the call has not responded. *)
Lemma startThreadIsPendingWhileItAdds_Proofs_complete : startThreadIsPendingWhileItAdds_Obl_complete.
Proof.
  intros heldIn history [N C] Hmade h code c t from a w [[Hcalled Hadds] (Haw & [ins Hbegun] & Hnotover)].
  destruct (method_begun (Member "ox.internal.ThreadHerd" "startThread" "scala.Function0:scala.Unit") C
    (Hmade h code from (or_introl (ex_intro _ c Hcalled))) eq_refl Hcalled) as (r & inside & Hh & Hcall).
  destruct (method_steps C (Member "ox.internal.ThreadHerd" "startThread" "scala.Function0:scala.Unit") Hcall Hh
    eq_refl) as (args0 & at_ & _ & _ & Hlater & _ & _).
  pose proof (Hlater a (makes_direct Hadds)) as Hfa.
  assert (ins = Some from) as -> by (destruct Hadds as [E | (? & ? & E)]; rewrite E in Hbegun; congruence).
  split; [lia | split; [exists inside; exact Hcall |]].
  intros (k & resp & sp & Hk & Hresp). apply Hnotover.
  assert (a < k) as Hak.
  { destruct (Z_lt_le_dec a k) as [H | H]; [exact H | exfalso]. destruct (Z.eq_dec a k) as [-> | Hne].
    - rewrite Hbegun in Hresp. discriminate Hresp.
    - assert (k < a) as Hka by lia.
      exact (method_over C (Member "ox.internal.ThreadHerd" "startThread" "scala.Function0:scala.Unit") Hcall Hh
        eq_refl Hresp Hka (makes_direct Hadds)). }
  apply (over_later history c a k w); [lia |].
  refine (method_meets
    (fun k => forall resp sp, history k = Event_Respond c from resp sp -> forall s t a, a < k ->
      history a = Event_Invoke c (Some from) (Invocation_mk
        "java.util.concurrent.ConcurrentHashMap$.KeySetView add java.lang.Object:scala.Boolean" [s; t]) ->
      overBy history c a k)
    C (Member "ox.internal.ThreadHerd" "startThread" "scala.Function0:scala.Unit") Hcall Hh eq_refl _ k
    ltac:(rewrite Hresp; cbn; auto) resp sp Hresp _ t a Hak Hbegun).
  intros args k' Hargs _. apply vals_one in Hargs as (vcode & -> & _).
  (* the two checks; the factory is read, and asked for a thread; the set is read *)
  pass. pass. pass. pass. pass.
  (* the add, and the response to it: from there on it is over *)
  step. intros wa ysa _ _ _ Hadd. split; [miss |]. intros wd rr x Hwd Hdn _ _.
  assert (forall j s t, wd <= j -> history wa = Event_Invoke c (Some from) (Invocation_mk
      "java.util.concurrent.ConcurrentHashMap$.KeySetView add java.lang.Object:scala.Boolean" [s; t]) ->
    overBy history c wa j) as Hover.
  { destruct Hdn as [(sp' & E & _) | (_ & Hlt & sp' & E)]; intros j s' t' Hj E'; [congruence |].
    exists (wd - 1), rr, sp'. split; [lia | exact E]. }
  (* it threw, or the thread is started: either way the call's response comes after *)
  step. 2: (intros; (split; [miss |]); intros; step).
  all: intros r' Hk' Hp He Hg resp' sp'' _ s' t' a' Ha' Ha''.
  all: pose proof (Hp a' Ha' ltac:(rewrite Ha''; cbn; auto)) as Hin; cbn [In] in Hin.
  all: repeat (destruct Hin as [<- | Hin]); try contradiction;
    first [apply (Hover _ s' t'); [lia | exact Ha''] | revert Ha''; miss].
Qed.

(** What it is from can hold: an execution in which nothing happens meets it. *)
Lemma startThreadIsPendingWhileItAdds_Proofs_feasible : startThreadIsPendingWhileItAdds_Obl_feasible.
Proof.
  exists (fun _ x => x), (fun _ => Event_Stutter).
  split; [exact rest_runs |].
  intros h code w [[who H] | [who H]]; destruct (nothing_called_at_rest _ _ _ H).
Qed.
