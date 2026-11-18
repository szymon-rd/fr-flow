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
