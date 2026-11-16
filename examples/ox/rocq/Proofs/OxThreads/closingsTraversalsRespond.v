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
      "java.util.concurrent.ConcurrentHashMap$.KeySetView forEach java.util.function.Consumer:scala.Unit"%string
      [heldIn "ox.internal.ThreadHerd threads"%string h; f]) (heldIn "ox.internal.ThreadHerd herdOwner"%string h) a)
    as Htrav.
  { destruct Hmakes as [E | (r & sp & E)]; [left; exists (Some from); exact E |].
    right. exists r, (Some from), sp. exact E. }
  apply (Htraversal (heldIn "ox.internal.ThreadHerd threads"%string h) f
    (heldIn "ox.internal.ThreadHerd herdOwner"%string h) a).
  split; [split; [exact Htrav | exact Hstops] |].
  intros x m Happ.
  destruct (Helements _ f _ x a m (conj Htrav Happ)) as (w & [Haw Hwm] & Hin).
  assert (calledBy history
    (Invocation_mk "java.util.function.Consumer accept java.lang.Object:scala.Unit"%string [f; x])
    (heldIn "ox.internal.ThreadHerd herdOwner"%string h) m) as Hacc.
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

(** What it is from can hold: an execution in which nothing happens, of sets with nothing in them, meets each. *)
Lemma closingsTraversalsRespond_Proofs_feasible : closingsTraversalsRespond_Obl_feasible.
Proof.
  exists (fun _ x => x), (fun _ => Event_Stutter), (fun _ _ _ => False).
  split; [exact rest_runs |].
  split.
  { intros h f x c k code made [[_ H] _]. destruct (nothing_called_at_rest _ _ _ H). }
  split.
  { intros s f c from [[H _] _]. destruct (nothing_called_at_rest _ _ _ H). }
  split.
  { intros s f c x from m [H _]. destruct (nothing_called_at_rest _ _ _ H). }
  split.
  { intros h x w b [_ H]. destruct H. }
  intros h w H. repeat (destruct H as [H | H]); destruct (nothing_called_on_at_rest _ _ _ H).
Qed.
