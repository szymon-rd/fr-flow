Require Export FrFlowGen.OxScopes.noForkIsMadeAfterItsScopeIsLeft.Spec.
Require Export Proofs.OxScopes.Lemmas.

(** The scope has ended at the step that would make the fork. Its maker would be inside the scope: it would have
    it open, which an ended scope is not; or be a fork of it not past its body, which an ended scope has none of. *)
Lemma noForkIsMadeAfterItsScopeIsLeft_Proofs_complete : noForkIsMadeAfterItsScopeIsLeft_Obl_complete.
Proof.
  intros taken atStart Hstart Hstep before by_ h between maker t after E.
  unfold startsSound_claim in Hstart. unfold everyStepCanBeTaken_claim in Hstep.
  pose proof (left_is_ended atStart taken Hstep before by_ h between (Step_Forks maker h t :: after) E) as Hended.
  assert (taken = (before ++ Step_Leave by_ h :: between) ++ Step_Forks maker h t :: after) as E'
    by (rewrite E, <- app_assoc; reflexivity).
  pose proof (sound_prefix atStart taken Hstart Hstep _ _ E') as Hsound.
  pose proof (Hstep _ _ _ E') as Hfork. cbn in Hfork.
  destruct Hsound as (((((Hcont & _) & _) & _) & _) & _).
  destruct Hended as (x & Hx & He).
  destruct Hfork as ([(x' & Hx' & _ & Hopen) | (f & Hf & Hsc & Hrun)] & _).
  - rewrite Hx in Hx'. injection Hx' as <-. contradiction.
  - destruct (Hcont h maker) as (f' & Hf' & Hfin).
    + split; [exists x; split; assumption | exists f; split; assumption].
    + rewrite Hf in Hf'. injection Hf' as <-. rewrite Hrun in Hfin. discriminate.
Qed.

(** A program with no scope and no fork that has taken no step meets what this is proven from. *)
Lemma noForkIsMadeAfterItsScopeIsLeft_Proofs_feasible : noForkIsMadeAfterItsScopeIsLeft_Obl_feasible.
Proof.
  exists nil. exists (Scopes_mk (fun _ => None) (fun _ => None) 0).
  split; [exact none_is_sound | exact (no_step_taken _)].
Qed.
