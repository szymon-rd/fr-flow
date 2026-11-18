Require Export FrFlowGen.OxThreads.callsNest.Spec.
Require Export Proofs.OxThreads.Lemmas.
From Stdlib Require Import ZArith Lia.

(** By how far the inner call is from the outer one. The inner call is one the outer made itself, and then the
    outer is responded to only once it is over; or it was begun while a call the outer made itself was pending:
    that one is over before the outer is responded to, it is nearer the inner call, and so the inner call is
    over before it is. *)
Lemma callsNest_Proofs_complete : callsNest_Obl_complete.
Proof.
  intros history _ Hends Hone by_ outer from inner m e [[[[Hbegun Hlt] Hpending] [ins Hinv]] Hover].
  assert (forall n from outer e, (Z.to_nat (m - from) <= n)%nat ->
    begun history outer by_ from -> from < m -> ~ overBy history by_ from m -> overBy history by_ from e ->
    overBy history by_ m e) as Hall.
  2: { exact (Hall _ from outer e (le_n _) Hbegun Hlt Hpending Hover). }
  clear from outer e Hbegun Hlt Hpending Hover.
  intros n. induction n as [| n IH]; intros from outer e Hn Hbegun Hlt Hpending (k & a & sp & Hk & Hresp);
    [exfalso; lia |].
  assert (m < k) as Hmk.
  { destruct (Z_lt_le_dec m k) as [Hlater | Hearlier]; [exact Hlater | exfalso].
    assert (k = m \/ k < m) as [-> | Hbefore] by lia.
    - rewrite Hinv in Hresp. discriminate Hresp.
    - apply Hpending. exists k, a, sp. split; [exact Hbefore | exact Hresp]. }
  assert (does history by_ ins m) as Hdoes by (unfold does; rewrite Hinv; split; reflexivity).
  destruct (Hone by_ outer from ins m (conj (conj (conj Hlt Hbegun) Hpending) Hdoes))
    as [-> | (between & m1 & [[[Hfm1 Hm1m] Hinv1] Hpending1])].
  - destruct (Hends by_ from a sp k inner m (conj (conj Hresp Hmk) Hinv)) as (k' & a' & sp' & Hk' & Hresp').
    exists k', a', sp'. split; [lia | exact Hresp'].
  - pose proof (Hends by_ from a sp k between m1 (conj (conj Hresp (Z.lt_trans _ _ _ Hm1m Hmk)) Hinv1))
      as Hover1.
    assert (Z.to_nat (m - m1) <= n)%nat as Hnearer by lia.
    destruct (IH m1 between k Hnearer (ex_intro _ (Some from) Hinv1) Hm1m Hpending1 Hover1)
      as (k' & a' & sp' & Hk' & Hresp').
    exists k', a', sp'. split; [lia | exact Hresp'].
Qed.

(** Its parts can hold together: an execution in which nothing happens meets each. *)
