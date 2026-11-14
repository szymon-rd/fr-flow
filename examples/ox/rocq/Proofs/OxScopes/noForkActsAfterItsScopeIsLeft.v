Require Export FrFlowGen.OxScopes.noForkActsAfterItsScopeIsLeft.Spec.
Require Export Proofs.OxScopes.Lemmas.

(** The scope is left, so it has ended, and stays ended through the steps between. The scopes are sound at each
    step, so every fork of the scope is past its body then; a fork that acts is not. *)
Lemma noForkActsAfterItsScopeIsLeft_Proofs_complete : noForkActsAfterItsScopeIsLeft_Obl_complete.
Proof.
  intros taken atStart Hstart Hstep before by_ h between t after E.
  unfold startsSound_claim in Hstart. unfold everyStepCanBeTaken_claim in Hstep.
  pose proof (left_is_ended atStart taken Hstep before by_ h between (Step_Act t h :: after) E) as Hended.
  assert (taken = (before ++ Step_Leave by_ h :: between) ++ Step_Act t h :: after) as E'
    by (rewrite E, <- app_assoc; reflexivity).
  pose proof (sound_prefix atStart taken Hstart Hstep _ _ E') as Hsound.
  pose proof (Hstep _ _ _ E') as Hact. cbn in Hact.
  destruct Hsound as (((((Hcont & _) & _) & _) & _) & _).
  destruct Hact as (f & Hf & Hsc & Hrun).
  destruct (Hcont h t) as (f' & Hf' & Hfin).
  - split; [exact Hended | exists f; split; assumption].
  - rewrite Hf in Hf'. injection Hf' as <-. rewrite Hrun in Hfin. discriminate.
Qed.

(** A program with no scope and no fork that has taken no step meets what this is proven from. *)
Lemma noForkActsAfterItsScopeIsLeft_Proofs_feasible : noForkActsAfterItsScopeIsLeft_Obl_feasible.
Proof.
  exists nil. exists (Scopes_mk (fun _ => None) (fun _ => None) 0).
  split; [exact none_is_sound | exact (no_step_taken _)].
Qed.
