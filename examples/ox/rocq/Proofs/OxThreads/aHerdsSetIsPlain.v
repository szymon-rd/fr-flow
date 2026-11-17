Require Export FrFlowGen.OxThreads.aHerdsSetIsPlain.Spec.
Require Export Proofs.OxThreads.Lemmas.

(** The herd's set is what `ConcurrentHashMap.newKeySet()` returned to the herd's constructor, so what is called
    on it is a method of a key set. Each such call is made by a method of the herd, or by a function startThread
    handed the factory, itself; and of a key set's methods those call only these five. *)
Lemma aHerdsSetIsPlain_Proofs_complete : aHerdsSetIsPlain_Obl_complete.
Proof.
  intros heldIn history _ Hkeeps Hkeyset Hcalls Hnew h w Hconstructed.
  destruct (Hnew h w Hconstructed) as (a & b & maker & Hmadeset).
  split; [exists a, b, maker; exact Hmadeset |].
  intros method w1 (rest & who & Hcalled).
  pose proof (Hkeyset _ a b (ex_intro _ maker Hmadeset) method w1
    (ex_intro _ rest (ex_intro _ who Hcalled))) as Hof.
  destruct (Hkeeps h w Hconstructed method rest who w1 Hcalled) as (i & Hmk & Hby).
  destruct (Hcalls h who i _ w1
    (conj (conj Hby Hmk) (ex_intro _ method (ex_intro _ _ (conj eq_refl Hof)))))
    as [[[[_ (s & t & E)] | [_ [(s & E) | (s & f & E)]]] | [_ (s & y & E)]] | [_ (s & t & E)]];
    inversion E; subst; repeat (first [reflexivity | right; reflexivity | left]).
Qed.

(** Its parts can hold together: an execution in which nothing happens meets each. *)
Lemma aHerdsSetIsPlain_Proofs_feasible : aHerdsSetIsPlain_Obl_feasible.
Proof.
  exists (fun _ x => x), (fun _ => Event_Stutter).
  split; [exact rest_runs |].
  split.
  { intros h w Hready. destruct (nothing_ready_at_rest _ _ _ Hready). }
  split.
  { intros s from to (who & H). destruct (nothing_completed_at_rest _ _ _ _ _ H). }
  split.
  { intros h c i made w [[_ H] _]. destruct H as [H | (a & spawns & H)]; discriminate H. }
  intros h w Hready. destruct (nothing_ready_at_rest _ _ _ Hready).
Qed.
