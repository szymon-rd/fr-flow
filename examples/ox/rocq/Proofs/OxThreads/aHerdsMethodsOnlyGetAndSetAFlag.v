Require Export FrFlowGen.OxThreads.aHerdsMethodsOnlyGetAndSetAFlag.Spec.
Require Export Proofs.OxThreads.Lemmas.

(** Each method of a herd has its list of the calls it makes itself, proven of its tree. Of those, the only ones
    of an atomic boolean's methods are the closing check's get and closing's set to true. *)
Lemma aHerdsMethodsOnlyGetAndSetAFlag_Proofs_complete : aHerdsMethodsOnlyGetAndSetAFlag_Obl_complete.
Proof.
  intros history _ Hclosing Howner Hmember Hstart Hcheck Htree h c i made w
    [[Hby Hmk] (method & taking & -> & Hof)].
  destruct Hby as [[[[[(x & Hb) | Hb] | (x & Hb)] | Hb] | Hb] | Hb].
  - destruct (Hstart h x i _ w (ex_intro _ c (conj Hb Hmk)))
      as [[[[H | H] | (f & r & H)] | (s & t & H)] | (t & H)];
      inversion H; subst; exfalso; repeat (destruct Hof as [Hof | Hof]; [| discriminate Hof]); discriminate Hof.
  - destruct (Hclosing h i _ w (ex_intro _ c (conj Hb Hmk))) as [[[H | (b & H)] | (s & H)] | (s & f & H)];
      inversion H; subst.
    + exfalso; repeat (destruct Hof as [Hof | Hof]; [| discriminate Hof]); discriminate Hof.
    + right. split; [exact (begun_is_called _ _ _ _ Hb) | exists b; reflexivity].
    + exfalso; repeat (destruct Hof as [Hof | Hof]; [| discriminate Hof]); discriminate Hof.
    + exfalso; repeat (destruct Hof as [Hof | Hof]; [| discriminate Hof]); discriminate Hof.
  - destruct (Hmember h x i _ w (ex_intro _ c (conj Hb Hmk))) as (s & y & H).
    inversion H; subst; exfalso; repeat (destruct Hof as [Hof | Hof]; [| discriminate Hof]); discriminate Hof.
  - destruct (Hcheck h i _ w (ex_intro _ c (conj Hb Hmk))) as (b & H). left. exists b. exact H.
  - destruct (Htree h i _ w (ex_intro _ c (conj Hb Hmk))) as [[[H | H] | (t & H)] | (f & scope & H)];
      inversion H; subst; exfalso; repeat (destruct Hof as [Hof | Hof]; [| discriminate Hof]); discriminate Hof.
  - pose proof (Howner h i _ w (ex_intro _ c (conj Hb Hmk))) as H.
    inversion H; subst; exfalso; repeat (destruct Hof as [Hof | Hof]; [| discriminate Hof]); discriminate Hof.
Qed.

(** Its parts can hold together: an execution in which nothing happens meets each. *)
