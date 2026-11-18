Require Export FrFlowGen.OxThreads.closingsTraversalsRespond.Spec.
Require Export Proofs.OxThreads.Lemmas.
From Stdlib Require Import String List ZArith Lia.

(** The traversal is responded to once each call of its function that it makes is, nothing more being added.
    Its function is applied only to what is in the set at a moment: a thread that was made to run code. And
    closing's functions, on such a thread, are responded to. *)
Lemma closingsTraversalsRespond_Proofs_complete : closingsTraversalsRespond_Obl_complete.
Proof.
  intros heldIn history elements _ Hfunctions Htraversal Helements Hmadetorun Hconstructed h f from a
    [[Hcalled Hmakes] Hstops].
  assert (calledBy history
    (Invocation_mk
      L.KeySetView_forEach
      [heldIn L.ThreadHerd_threads h; f]) (heldIn L.ThreadHerd_herdOwner h) a)
    as Htrav.
  { destruct Hmakes as [E | (r & sp & E)]; [left; exists (Some from); exact E |].
    right. exists r, (Some from), sp. exact E. }
  apply (Htraversal (heldIn L.ThreadHerd_threads h) f
    (heldIn L.ThreadHerd_herdOwner h) a).
  split; [split; [exact Htrav | exact Hstops] |].
  intros x m Happ.
  destruct (Helements _ f _ x a m (conj Htrav Happ)) as (w & [Haw Hwm] & Hin).
  assert (calledBy history
    (Invocation_mk L.Consumer_accept [f; x])
    (heldIn L.ThreadHerd_herdOwner h) m) as Hacc.
  { destruct Happ as [E | (r & sp & E)]; [left; exists (Some a); exact E |].
    right. exists r, (Some a), sp. exact E. }
  assert (a < m) as Hlt.
  { destruct (Z.eq_dec a m) as [-> | Hne]; [| lia].
    destruct (one_call_at_a_moment _ _ _ _ _ _ Htrav Hacc) as [E _]. discriminate E. }
  destruct (Hmadetorun h x w from) as (code & made & Hmr).
  { split; [| exact Hin]. apply (Hconstructed h from). do 4 left. right. unfold calledOn. eauto 14. }
  apply (Hfunctions h f x _ m code made). split; [split; [| exact Hacc] | exact Hmr].
  exists from, a. split; [split; [exact Hlt | exact Hcalled] | exact Hmakes].
Qed.
