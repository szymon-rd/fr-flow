Require Export FrFlowGen.OxThreads.aHerdsFlagIsOnlyReadAndSet.Spec.
Require Export Proofs.OxThreads.Lemmas.

(** The herd's flag is what `new AtomicBoolean(false)` returned to the herd's constructor, so what is called on
    it is a method of an atomic boolean. Each such call is made by one of the herd's methods, itself; and of an
    atomic boolean's methods those call only get and set. *)
Lemma aHerdsFlagIsOnlyReadAndSet_Proofs_complete : aHerdsFlagIsOnlyReadAndSet_Obl_complete.
Proof.
  intros heldIn history _ Hkeeps Hbool Hmethods Hnew h w Hconstructed method w1 (rest & who & Hcalled).
  destruct (Hnew h w Hconstructed) as (a & b & maker & Hflag).
  pose proof (Hbool _ False a b (ex_intro _ maker Hflag) method w1
    (ex_intro _ rest (ex_intro _ who Hcalled))) as Hof.
  destruct (Hkeeps h w Hconstructed method rest who w1 Hcalled) as (i & Hmk & [Hby | []]).
  destruct (Hmethods h who i _ w1
    (conj (conj Hby Hmk) (ex_intro _ method (ex_intro _ _ (conj eq_refl Hof)))))
    as [(flag & E) | [_ (flag & E)]]; inversion E; subst; [left | right]; reflexivity.
Qed.

(** Its parts can hold together: an execution in which nothing happens meets each. *)
Lemma aHerdsFlagIsOnlyReadAndSet_Proofs_feasible : aHerdsFlagIsOnlyReadAndSet_Obl_feasible.
Proof.
  exists (fun _ x => x), (fun _ => Event_Stutter).
  split; [exact rest_runs |].
  split.
  { intros h w Hready. destruct (nothing_ready_at_rest _ _ _ Hready). }
  split.
  { intros b x from to (who & H). destruct (nothing_completed_at_rest _ _ _ _ _ H). }
  split.
  { intros h c i made w [[_ H] _]. destruct H as [H | (a & spawns & H)]; discriminate H. }
  intros h w Hready. destruct (nothing_ready_at_rest _ _ _ Hready).
Qed.
