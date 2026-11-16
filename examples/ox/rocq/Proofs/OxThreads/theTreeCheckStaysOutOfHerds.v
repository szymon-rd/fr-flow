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
    (fun made => (((made = Invocation_mk "java.lang.Thread$ currentThread :java.lang.Thread" [] \/
        made = Invocation_mk "java.lang.ThreadLocal get :java.lang.Object" []) \/
        (exists t, made = Invocation_mk "java.lang.Thread getName :java.lang.String" [t])) \/
        (exists f scope, made = Invocation_mk "scala.Function apply" [f; scope])) /\
      (forall f scope, made = Invocation_mk "scala.Function apply" [f; scope] -> walksUp history f))
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

(** Its parts can hold together: an execution in which nothing happens meets each. *)
Lemma theTreeCheckStaysOutOfHerds_Proofs_feasible : theTreeCheckStaysOutOfHerds_Obl_feasible.
Proof.
  exists (fun _ x => x), (fun _ => Event_Stutter).
  split; [exact rest_runs |].
  split.
  { intros h from inner w (who & H & _). destruct (nothing_begun_at_rest _ _ _ H). }
  split.
  { intros g scope _ h x. split; intros who from w [[_ H] _]; destruct (nothing_begun_at_rest _ _ _ H). }
  split.
  { intros t s x. repeat (intros; split). all: intros who from w [[_ H] _]; destruct (nothing_begun_at_rest _ _ _ H). }
  intros t outer from inside w [[[_ H] _] _]. destruct (nothing_begun_at_rest _ _ _ H).
Qed.
