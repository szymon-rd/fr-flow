Require Export FrFlowGen.OxThreads.closingEndsOnEmpty.Spec.
Require Export Proofs.OxThreads.Lemmas.

(** Closing completes only after the set answered that it is empty; nothing is added while it is asked; and a
    set that answers so, with nothing added meanwhile, is empty at a moment of the call that asked. *)
Lemma closingEndsOnEmpty_Proofs_complete : closingEndsOnEmpty_Obl_complete.
Proof.
  intros heldIn history elements _ Hfound Hempty Hquiet h from response to Hdone.
  destruct (Hfound h from response to Hdone) as (a & b & [Ha Hb] & Hask).
  destruct (Hempty _ a _ b (ex_intro (fun who => completedBy history _ who a _ b) _ Hask)
    (conj eq_refl (Hquiet h a b Hask))) as (m & [Hm1 Hm2] & Hnone).
  exists m. split; [lia | exact Hnone].
Qed.

(** Its parts can hold together: an execution in which nothing happens meets each. *)
