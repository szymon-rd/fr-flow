Require Export FrFlowGen.OxScopes.scopesAreLeftInsideOut.Spec.
Require Export Proofs.OxScopes.Lemmas.

(** The scope is left, so it has ended; the scopes are sound then, and in sound scopes a scope opened inside
    one that has ended has ended. *)
Lemma scopesAreLeftInsideOut_Proofs_complete : scopesAreLeftInsideOut_Obl_complete.
Proof.
  intros atStart taken Hstart Hstep before by_ h after inner (E & Hinside).
  unfold startsSound_claim in Hstart. unfold everyStepCanBeTaken_claim in Hstep.
  pose proof (sound_prefix atStart taken Hstart Hstep _ _ E) as Hsound.
  pose proof (Hstep _ _ _ E) as Hleave. cbn in Hleave.
  destruct Hsound as (((((_ & Hnest) & _) & _) & _) & _).
  apply (Hnest h inner). split; [exact Hinside |].
  destruct Hleave as (x & Hx & _ & He). exists x. split; assumption.
Qed.

(** A program with no scope and no fork that has taken no step meets what this is proven from. *)
Lemma scopesAreLeftInsideOut_Proofs_feasible : scopesAreLeftInsideOut_Obl_feasible.
Proof.
  exists (Scopes_mk (fun _ => None) (fun _ => None) 0). exists nil.
  split; [exact none_is_sound | exact (no_step_taken _)].
Qed.
