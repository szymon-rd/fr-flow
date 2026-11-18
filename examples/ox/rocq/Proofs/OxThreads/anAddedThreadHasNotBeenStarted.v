Require Export FrFlowGen.OxThreads.anAddedThreadHasNotBeenStarted.Spec.
Require Export Proofs.OxThreads.Lemmas.

(** The add is made by a call of `startThread` itself; the thread is the one its factory made for it; such a
    thread is started only by that call itself; and that call adds before it starts. *)
Lemma anAddedThreadHasNotBeenStarted_Proofs_complete : anAddedThreadHasNotBeenStarted_Obl_complete.
Proof.
  intros heldIn history _ Honly Hmaker Hmade Hbefore h t c w b Hadd (m & Hm & who & Hstart).
  destruct (Honly h t c w b Hadd) as (code & from & Hcalled & Hitself).
  pose proof (Hmade h code c t from w (conj Hcalled Hitself)) as Hfor.
  pose proof (Hmaker h code c t from w m who (conj (conj Hcalled Hfor) Hstart)) as Hown.
  pose proof (Hbefore h code c t from w m t (conj (conj Hcalled Hitself) Hown)). lia.
Qed.

(** What it is from can hold: an execution in which nothing happens meets it. *)
