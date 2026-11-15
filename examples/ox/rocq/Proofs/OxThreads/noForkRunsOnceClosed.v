Require Export FrFlowGen.OxThreads.noForkRunsOnceClosed.Spec.
Require Export Proofs.OxThreads.Lemmas.

(** Once a herd is closed a fork has left. It called its code only before leaving, and no call of it was pending
    when it left. *)
Lemma noForkRunsOnceClosed_Proofs_complete : noForkRunsOnceClosed_Obl_complete.
Proof.
  intros heldIn history _ Hleft Hcode h t code w [Hclosed Hmade].
  assert (hasLeft heldIn history t h w) as (r & Hr & who & Hrem).
  { apply Hleft. split; [exact Hclosed |]. destruct Hmade as (c & from & added & to & [Hto Hdone] & _).
    exists from, added, to. split; [exact Hto | exists c; exact Hdone]. }
  destruct (Hcode h t code w r Hmade) as [_ Hnotpending].
  split.
  - intros (m1 & Hm1 & Hbegun & Hpending).
    destruct (Hcode h t code w m1 Hmade) as [Hbefore _].
    assert (~ hasLeft heldIn history t h m1) as Hstays by (apply Hbefore; apply begun_is_called; exact Hbegun).
    assert (m1 < r \/ m1 = r \/ r < m1) as [Hlt | [-> | Hgt]] by lia.
    + apply Hnotpending; [exists who; exact Hrem |]. exists m1. split; [exact Hlt | split; [exact Hbegun |]].
      intros Hover. apply Hpending. apply (over_later history t m1 r w); [lia | exact Hover].
    + destruct (one_call_at_a_moment history _ _ _ _ r Hrem (begun_is_called _ _ _ _ Hbegun)) as [E _].
      discriminate E.
    + apply Hstays. exists r. split; [exact Hgt | exists who; exact Hrem].
  - intros Hc. destruct (Hcode h t code w w Hmade) as [Hbefore _]. apply (Hbefore Hc).
    exists r. split; [exact Hr | exists who; exact Hrem].
Qed.

(** Its parts can hold together: a run in which nothing happens meets each. *)
Lemma noForkRunsOnceClosed_Proofs_feasible : noForkRunsOnceClosed_Obl_feasible.
Proof.
  exists (fun _ x => x), (fun _ => Event_Stutter).
  split; [exact rest_runs |].
  split.
  { intros h t w [_ H]. destruct (no_fork_at_rest _ _ _ _ H). }
  intros h t code made w H. destruct (none_made_to_run_at_rest _ _ _ _ _ H).
Qed.
