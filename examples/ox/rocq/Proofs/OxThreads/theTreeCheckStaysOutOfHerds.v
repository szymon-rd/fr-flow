Require Export FrFlowGen.OxThreads.theTreeCheckStaysOutOfHerds.Spec.
Require Export Proofs.OxThreads.Lemmas.

(** What the thread calls while it is calling the tree check is one of the four calls the check makes itself,
    none of which is closing or remove, or is called while one of those is pending: three are of the JDK, which
    calls into no herd, and the fourth applies the function that goes up the scopes, of which the same is
    proven. *)
Lemma theTreeCheckStaysOutOfHerds_Proofs_complete : theTreeCheckStaysOutOfHerds_Obl_complete.
Proof.
  intros heldIn history _ Hlist Hwalk Hjdk Hone h h1 x.
  split; intros who from w Hpending Hcalled.
  all: destruct (called_under history
    (fun made => (((made = Invocation_mk L.Thread_currentThread [] \/
        made = Invocation_mk L.ThreadLocal_get []) \/
        (exists t, made = Invocation_mk L.Thread_getName [t])) \/
        (exists f scope, made = Invocation_mk L.Function_apply [f; scope])) /\
      (forall f scope, made = Invocation_mk L.Function_apply [f; scope] -> walksUp history f))
    who _ from _ w (Hone who)
    (fun made k Hmade => conj
      (Hlist h from made k (ex_intro _ who (conj (proj2 (proj1 Hpending)) Hmade)))
      (fun f scope E => ex_intro _ h (ex_intro _ who (ex_intro _ scope (ex_intro _ from (ex_intro _ k
        (conj (or_introl (proj2 (proj1 Hpending))) (eq_ind _ (fun i => itselfMakes history i who from k)
          Hmade _ E))))))))
    Hpending Hcalled) as [[Hown _] | (between & m & [Hallowed Hwalks] & Hunder)].
  1, 3: destruct Hown as [[[E | E] | (t & E)] | (f & scope & E)]; discriminate E.
  all: destruct Hallowed as [[[-> | ->] | (t & ->)] | (f & scope & ->)].
  - exact (proj1 (proj1 (proj1 (proj1 (Hjdk who who who))) h1 x) who m w Hunder Hcalled).
  - exact (proj1 (proj2 (proj1 (proj1 (Hjdk who who who))) h1 x) who m w Hunder Hcalled).
  - exact (proj1 (proj2 (proj1 (Hjdk t who who)) h1 x) who m w Hunder Hcalled).
  - exact (proj1 (Hwalk f scope (Hwalks f scope eq_refl) h1 x) who m w Hunder Hcalled).
  - exact (proj2 (proj1 (proj1 (proj1 (Hjdk who who who))) h1 x) who m w Hunder Hcalled).
  - exact (proj2 (proj2 (proj1 (proj1 (Hjdk who who who))) h1 x) who m w Hunder Hcalled).
  - exact (proj2 (proj2 (proj1 (Hjdk t who who)) h1 x) who m w Hunder Hcalled).
  - exact (proj2 (Hwalk f scope (Hwalks f scope eq_refl) h1 x) who m w Hunder Hcalled).
Qed.
