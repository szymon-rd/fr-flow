Require Export FrFlowGen.OxScopes.Whole.Spec.
Require Export Proofs.OxScopes.Lemmas.

(** What the statements about a program's scopes say can be so. A program with no scope and no fork that has
    taken no step starts sound, and every step it took could be taken. A program can leave a scope with another
    opened inside it; and a program can take a step. *)

Lemma Whole_Proofs_consistent_0 : Whole_Obl_consistent_0.
Proof.
  exists (Scopes_mk (fun _ => None) (fun _ => None) 0). exists nil.
  split; [exact none_is_sound | exact (no_step_taken _)].
Qed.

Lemma Whole_Proofs_satisfiable_1_scopesAreLeftInsideOut : Whole_Obl_satisfiable_1_scopesAreLeftInsideOut.
Proof.
  exists (Scopes_mk (fun _ => Some (Scope_mk 0 (Some 1) 0 True)) (fun _ => None) 1).
  exists (Step_Leave 0 1 :: nil). exists nil. exists 0. exists 1. exists nil. exists 0.
  repeat split. eexists. split; reflexivity.
Qed.

Lemma Whole_Proofs_satisfiable_1_everyStepCanBeTaken : Whole_Obl_satisfiable_1_everyStepCanBeTaken.
Proof.
  exists (Step_Leave 0 0 :: nil). exists nil. exists (Step_Leave 0 0). exists nil. repeat split.
Qed.
