Require Export FrFlowGen.OxScopes.Domain.
From Stdlib Require Import Lia List.

(** What the system of scopes keeps, whatever program takes its steps.

    `sound_step`: a step that can be taken leaves sound scopes sound. Each kind of step is taken in turn, and for
    each the six parts of soundness. The two that matter:
    - a fork made in a scope: the scope has not ended, since its maker is inside it (it has it open, or is a
      fork of it not past its body, which an ended scope has none of);
    - a scope ended: every scope opened inside it has ended. One opened by the same thread and still open would
      be the thread's innermost, not this one; one opened by a fork of it would be open in a fork past its body. *)

Lemma sound_step (s : Scopes) (e : Step) : sound s -> canTake s e -> sound (afterStep s e).
Proof.
  intros Hs Hc. destruct s as [sc fk ck].
  destruct e as [by_ h0 par | by_ h0 c | t | by_ h0 | by_ h0 | t h0].
  6: exact Hs.
  5: exact Hs.
  - (* a scope opened *)
    autounfold with frflow_defs in *. cbn in *.
    destruct Hs as (((((Hcont & Hnest) & Hfin) & Hpar) & Hfs) & Hclk).
    destruct Hc as ((Hfresh & Hlive) & Hin).
    destruct (sc h0) eqn:E0; [contradiction |].
    repeat split.
    + intros h t [(x & Hx & He) (f & Hf & Hsc)].
      destruct (Z.eq_dec h h0) as [-> | Hne].
      * rewrite ite_true in Hx by reflexivity. injection Hx as <-. contradiction.
      * rewrite ite_false in Hx by exact Hne. apply (Hcont h t). split; eauto.
    + intros h inner [(x & Hx & Hp) (y & Hy & He)].
      destruct (Z.eq_dec h h0) as [-> | Hne].
      { rewrite ite_true in Hy by reflexivity. injection Hy as <-. contradiction. }
      rewrite ite_false in Hy by exact Hne.
      destruct (Z.eq_dec inner h0) as [-> | Hni].
      * rewrite ite_true in Hx by reflexivity. injection Hx as <-. cbn in Hp. subst par.
        destruct Hin as [[(x' & Hx' & _ & Hopen) _] | [_ (f & Hf & Hsc & Hrun)]].
        -- rewrite Hy in Hx'. injection Hx' as <-. contradiction.
        -- destruct (Hcont h by_) as (f' & Hf' & Hfin'); [split; eauto |].
           rewrite Hf in Hf'. injection Hf' as <-. rewrite Hrun in Hfin'. discriminate.
      * rewrite ite_false in Hx by exact Hni. rewrite ite_false by exact Hni.
        apply (Hnest h inner). split; eauto.
    + intros t h (f & Hf & Hl) (x & Hx & Ho & Hnot).
      destruct (Z.eq_dec h h0) as [-> | Hne].
      * rewrite ite_true in Hx by reflexivity. injection Hx as <-. cbn in Ho. subst t.
        rewrite (Hlive f Hf) in Hl. discriminate.
      * rewrite ite_false in Hx by exact Hne. apply (Hfin t h); eauto.
    + intros h inner x Hx Hp.
      destruct (Z.eq_dec inner h0) as [-> | Hni].
      * rewrite ite_true in Hx by reflexivity. injection Hx as <-. cbn in Hp. subst par. cbn.
        destruct Hin as [[(x' & Hx' & Ho & _) _] | [_ (f & Hf & Hsc & Hrun)]].
        -- assert (h <> h0) as Hne by (intros ->; rewrite E0 in Hx'; discriminate).
           rewrite ite_false by exact Hne. exists x'. repeat split; [exact Hx' | exact (Hclk h x' Hx') | left; exact Ho].
        -- destruct (sc h) as [p |] eqn:Eh; [| exfalso; apply (Hfs by_ h); eauto].
           assert (h <> h0) as Hne by (intros ->; rewrite E0 in Eh; discriminate).
           rewrite ite_false by exact Hne. exists p. repeat split; [exact (Hclk h p Eh) | right; eauto].
      * rewrite ite_false in Hx by exact Hni.
        destruct (Hpar h inner x Hx Hp) as (p & Hp' & Hlt & Hor).
        assert (h <> h0) as Hne by (intros ->; rewrite E0 in Hp'; discriminate).
        rewrite ite_false by exact Hne. exists p. auto.
    + intros t h Hfork. destruct (Z.eq_dec h h0) as [-> | Hne].
      * rewrite ite_true by reflexivity. discriminate.
      * rewrite ite_false by exact Hne. apply (Hfs t h Hfork).
    + intros h x Hx. destruct (Z.eq_dec h h0) as [-> | Hne].
      * rewrite ite_true in Hx by reflexivity. injection Hx as <-. cbn. lia.
      * rewrite ite_false in Hx by exact Hne. pose proof (Hclk h x Hx). lia.
  - (* a fork made *)
    autounfold with frflow_defs in *. cbn in *.
    destruct Hs as (((((Hcont & Hnest) & Hfin) & Hpar) & Hfs) & Hclk).
    destruct Hc as (Hin & Hnofork & Howns).
    destruct (fk c) eqn:Ec; [contradiction |].
    repeat split.
    + intros h t [(x & Hx & He) (f & Hf & Hsc)].
      destruct (Z.eq_dec t c) as [-> | Hne].
      * rewrite ite_true in Hf by reflexivity. injection Hf as <-. cbn in Hsc. subst h.
        destruct Hin as [(x' & Hx' & _ & Hopen) | (g & Hg & Hgs & Hrun)].
        -- rewrite Hx in Hx'. injection Hx' as <-. contradiction.
        -- destruct (Hcont h0 by_) as (g' & Hg' & Hfin'); [split; eauto |].
           rewrite Hg in Hg'. injection Hg' as <-. rewrite Hrun in Hfin'. discriminate.
      * rewrite ite_false in Hf by exact Hne. rewrite ite_false by exact Hne.
        apply (Hcont h t). split; eauto.
    + exact Hnest.
    + intros t h (f & Hf & Hl) Hex.
      destruct (Z.eq_dec t c) as [-> | Hne].
      * rewrite ite_true in Hf by reflexivity. injection Hf as <-. discriminate.
      * rewrite ite_false in Hf by exact Hne. apply (Hfin t h); eauto.
    + intros h inner x Hx Hp. destruct (Hpar h inner x Hx Hp) as (p & Hp' & Hlt & Hor).
      exists p. repeat split; [exact Hp' | exact Hlt |].
      destruct Hor as [Ho | Hfork]; [left; exact Ho | right].
      rewrite ite_false by (exact (Howns inner x Hx)). exact Hfork.
    + intros t h (f & Hf & Hsc).
      destruct (Z.eq_dec t c) as [-> | Hne].
      * rewrite ite_true in Hf by reflexivity. injection Hf as <-. cbn in Hsc. subst h.
        destruct Hin as [(x' & Hx' & _) | (g & Hg & Hgs & _)].
        -- rewrite Hx'. discriminate.
        -- apply (Hfs by_ h0). eauto.
      * rewrite ite_false in Hf by exact Hne. apply (Hfs t h). eauto.
    + exact Hclk.
  - (* a fork past its body *)
    autounfold with frflow_defs in *. cbn in *.
    destruct Hs as (((((Hcont & Hnest) & Hfin) & Hpar) & Hfs) & Hclk).
    destruct Hc as ((f0 & Hf0 & Hrun) & Hnone).
    rewrite Hf0. cbn.
    repeat split.
    + intros h u [(x & Hx & He) (g & Hg & Hsc)].
      destruct (Z.eq_dec u t) as [-> | Hne].
      * rewrite ite_true in Hg by reflexivity. rewrite ite_true by reflexivity.
        injection Hg as <-. eexists. split; reflexivity.
      * rewrite ite_false in Hg by exact Hne. rewrite ite_false by exact Hne.
        apply (Hcont h u). split; eauto.
    + exact Hnest.
    + intros u h (g & Hg & Hl) Hex.
      destruct (Z.eq_dec u t) as [-> | Hne].
      * apply (Hnone h). exact Hex.
      * rewrite ite_false in Hg by exact Hne. apply (Hfin u h); eauto.
    + intros h inner x Hx Hp. destruct (Hpar h inner x Hx Hp) as (p & Hp' & Hlt & Hor).
      exists p. repeat split; [exact Hp' | exact Hlt |].
      destruct Hor as [Ho | (g & Hg & Hsc)]; [left; exact Ho | right].
      destruct (Z.eq_dec (Scope_owner x) t) as [E | Hne].
      * rewrite ite_true by exact E. rewrite E in Hg. rewrite Hf0 in Hg. injection Hg as <-.
        eexists. split; [reflexivity | exact Hsc].
      * rewrite ite_false by exact Hne. eauto.
    + intros u h (g & Hg & Hsc).
      destruct (Z.eq_dec u t) as [-> | Hne].
      * rewrite ite_true in Hg by reflexivity. injection Hg as <-. cbn in Hsc.
        apply (Hfs t h). eauto.
      * rewrite ite_false in Hg by exact Hne. apply (Hfs u h). eauto.
    + exact Hclk.
  - (* a scope ended *)
    autounfold with frflow_defs in *. cbn in *.
    destruct Hs as (((((Hcont & Hnest) & Hfin) & Hpar) & Hfs) & Hclk).
    destruct Hc as (((x0 & Hx0 & Ho0 & Hopen0) & Hinner) & Hall).
    rewrite Hx0. cbn.
    repeat split.
    + intros h t [(x & Hx & He) (f & Hf & Hsc)].
      destruct (Z.eq_dec h h0) as [-> | Hne].
      * exists f. split; [exact Hf | exact (Hall t f Hf Hsc)].
      * rewrite ite_false in Hx by exact Hne. apply (Hcont h t). split; eauto.
    + intros h inner [(x & Hx & Hp) (y & Hy & He)].
      destruct (Z.eq_dec inner h0) as [-> | Hni].
      { rewrite ite_true by reflexivity. eexists. split; [reflexivity | exact I]. }
      rewrite ite_false in Hx by exact Hni. rewrite ite_false by exact Hni.
      destruct (Z.eq_dec h h0) as [-> | Hne].
      * destruct (Hpar h0 inner x Hx Hp) as (p & Hp' & Hlt & Hor).
        rewrite Hx0 in Hp'. injection Hp' as <-.
        destruct (classic (Scope_ended x)) as [Hended | Hnot]; [eauto |]. exfalso.
        destruct Hor as [Ho | (f & Hf & Hsc)].
        -- assert (exists x1, sc inner = Some x1 /\ Scope_owner x1 = by_ /\ ~ Scope_ended x1) as Hhas
             by (exists x; repeat split; [exact Hx | congruence | exact Hnot]).
           pose proof (Hinner inner Hhas) as Hle. rewrite Hx in Hle. rewrite Hx0 in Hle. lia.
        -- apply (Hfin (Scope_owner x) inner).
           ++ exists f. split; [exact Hf | exact (Hall _ f Hf Hsc)].
           ++ exists x. auto.
      * rewrite ite_false in Hy by exact Hne. apply (Hnest h inner). split; eauto.
    + intros t h (f & Hf & Hl) (x & Hx & Ho & Hnot).
      destruct (Z.eq_dec h h0) as [-> | Hne].
      * rewrite ite_true in Hx by reflexivity. injection Hx as <-. apply Hnot. exact I.
      * rewrite ite_false in Hx by exact Hne. apply (Hfin t h); eauto.
    + intros h inner x Hx Hp.
      destruct (Z.eq_dec inner h0) as [-> | Hni].
      * rewrite ite_true in Hx by reflexivity. injection Hx as <-. cbn in Hp |- *.
        destruct (Hpar h h0 x0 Hx0 Hp) as (p & Hp' & Hlt & Hor).
        destruct (Z.eq_dec h h0) as [-> | Hne].
        -- rewrite Hx0 in Hp'. injection Hp' as <-. lia.
        -- rewrite ite_false by exact Hne. exists p. auto.
      * rewrite ite_false in Hx by exact Hni.
        destruct (Hpar h inner x Hx Hp) as (p & Hp' & Hlt & Hor).
        destruct (Z.eq_dec h h0) as [-> | Hne].
        -- rewrite ite_true by reflexivity. rewrite Hx0 in Hp'. injection Hp' as <-.
           eexists. split; [reflexivity |]. cbn. auto.
        -- rewrite ite_false by exact Hne. exists p. auto.
    + intros t h Hfork. destruct (Z.eq_dec h h0) as [-> | Hne].
      * rewrite ite_true by reflexivity. discriminate.
      * rewrite ite_false by exact Hne. apply (Hfs t h Hfork).
    + intros h x Hx. destruct (Z.eq_dec h h0) as [-> | Hne].
      * rewrite ite_true in Hx by reflexivity. injection Hx as <-. cbn. exact (Hclk h0 x0 Hx0).
      * rewrite ite_false in Hx by exact Hne. exact (Hclk h x Hx).
Qed.

(** ** Along the steps a program takes *)

Lemma ran_nil (s : Scopes) : ran s nil = s.
Proof. reflexivity. Qed.

Lemma ran_app (s : Scopes) (pre post : list Step) : ran s (pre ++ post) = ran (ran s pre) post.
Proof. unfold ran. apply List_foldl_app. Qed.

Lemma ran_snoc (s : Scopes) (pre : list Step) (e : Step) : ran s (pre ++ e :: nil) = afterStep (ran s pre) e.
Proof. rewrite ran_app. reflexivity. Qed.

(** When a program starts sound and takes only steps that can be taken, its scopes are sound after each. *)
Lemma sound_prefix (atStart : Scopes) (taken : list Step) :
  sound atStart ->
  (forall before e after, tookBetween taken before e after -> canTake (ran atStart before) e) ->
  forall before after, taken = before ++ after -> sound (ran atStart before).
Proof.
  intros H0 Hstep before. induction before as [| e before IH] using rev_ind; intros after E.
  - exact H0.
  - rewrite ran_snoc. apply sound_step.
    + apply (IH (e :: after)). rewrite E, <- app_assoc. reflexivity.
    + apply (Hstep before e after). unfold tookBetween. rewrite E, <- app_assoc. reflexivity.
Qed.

(** A scope that has ended stays ended. *)
Lemma ended_step (s : Scopes) (e : Step) (h : Z) : canTake s e -> ended s h -> ended (afterStep s e) h.
Proof.
  intros Hc (x & Hx & He). destruct s as [sc fk ck].
  destruct e as [by_ h0 par | by_ h0 c | t | by_ h0 | by_ h0 | t h0];
    autounfold with frflow_defs in *; cbn in *; try (exists x; split; assumption).
  - destruct Hc as ((Hfresh & _) & _). destruct (Z.eq_dec h h0) as [-> | Hne].
    + rewrite Hx in Hfresh. contradiction.
    + exists x. rewrite ite_false by exact Hne. split; assumption.
  - destruct Hc as (((x0 & Hx0 & _) & _) & _). rewrite Hx0. cbn.
    destruct (Z.eq_dec h h0) as [-> | Hne].
    + eexists. rewrite ite_true by reflexivity. split; [reflexivity | exact I].
    + exists x. rewrite ite_false by exact Hne. split; assumption.
Qed.

Lemma ended_later (atStart : Scopes) (taken : list Step) :
  (forall before e after, tookBetween taken before e after -> canTake (ran atStart before) e) ->
  forall before between after h, taken = before ++ between ++ after ->
    ended (ran atStart before) h -> ended (ran atStart (before ++ between)) h.
Proof.
  intros Hstep before between. induction between as [| e between IH] using rev_ind; intros after h E He.
  - rewrite app_nil_r. exact He.
  - rewrite app_assoc, ran_snoc. apply ended_step.
    + apply (Hstep (before ++ between) e after). unfold tookBetween. rewrite E, <- !app_assoc. reflexivity.
    + apply (IH (e :: after) h); [| exact He]. rewrite E, <- !app_assoc. reflexivity.
Qed.

(** After a scope is left, it has ended at every later step. *)
Lemma left_is_ended (atStart : Scopes) (taken : list Step) :
  (forall before e after, tookBetween taken before e after -> canTake (ran atStart before) e) ->
  forall before by_ h between after, taken = before ++ Step_Leave by_ h :: between ++ after ->
    ended (ran atStart (before ++ Step_Leave by_ h :: between)) h.
Proof.
  intros Hstep before by_ h between after E.
  apply (ended_later atStart taken Hstep before (Step_Leave by_ h :: between) after h); [exact E |].
  assert (canTake (ran atStart before) (Step_Leave by_ h)) as Hc
    by (apply (Hstep before _ (between ++ after)); exact E).
  cbn in Hc. destruct Hc as (x & Hx & _ & He). exists x. split; assumption.
Qed.

(** ** A program there can be: no scope, no fork, no step taken *)

Lemma none_is_sound : sound (Scopes_mk (fun _ => None) (fun _ => None) 0).
Proof.
  autounfold with frflow_defs. cbn.
  repeat split; intros;
    repeat match goal with
      | H : exists _, _ |- _ => destruct H
      | H : _ /\ _ |- _ => destruct H
      end; discriminate.
Qed.

Lemma no_step_taken (atStart : Scopes) :
  forall before e after, tookBetween nil before e after -> canTake (ran atStart before) e.
Proof. intros before e after E. unfold tookBetween in E. destruct before; discriminate. Qed.

(** ** What each kind of step changes *)

Lemma open_scope (s : Scopes) (w h : Z) (p : option Z) (k : Z) :
  scope_of (afterStep s (Step_Open w h p)) k =
    ite (k = h) (Some (Scope_mk w p (clock_of s) False)) (scope_of s k).
Proof. destruct s. reflexivity. Qed.

Lemma open_fork (s : Scopes) (w h : Z) (p : option Z) : fork_of (afterStep s (Step_Open w h p)) = fork_of s.
Proof. destruct s. reflexivity. Qed.

Lemma open_hasOpen (s : Scopes) (w h : Z) (p : option Z) (w' h' : Z) :
  scope_of s h = None ->
  hasOpen (afterStep s (Step_Open w h p)) w' h' <-> (w' = w /\ h' = h) \/ hasOpen s w' h'.
Proof.
  intro Hfresh. unfold hasOpen. rewrite open_scope. destruct (Z.eq_dec h' h) as [-> | Hne].
  - rewrite ite_true by reflexivity. split.
    + intros (x & Hx & Ho & _). injection Hx as <-. left. split; [symmetry; exact Ho | reflexivity].
    + intros [[-> _] | (x & Hx & _)]; [| rewrite Hfresh in Hx; discriminate].
      eexists. split; [reflexivity |]. cbn. split; [reflexivity | tauto].
  - rewrite ite_false by exact Hne. split; [tauto |]. intros [[_ E] | H]; [contradiction | exact H].
Qed.

Lemma open_openedAt (s : Scopes) (w h : Z) (p : option Z) (h' : Z) :
  openedAt (afterStep s (Step_Open w h p)) h' = ite (h' = h) (clock_of s) (openedAt s h').
Proof.
  unfold openedAt. rewrite open_scope. destruct (Z.eq_dec h' h) as [-> | Hne].
  - rewrite !ite_true by reflexivity. reflexivity.
  - rewrite !ite_false by exact Hne. reflexivity.
Qed.

Lemma forks_scope (s : Scopes) (w h c : Z) : scope_of (afterStep s (Step_Forks w h c)) = scope_of s.
Proof. destruct s. reflexivity. Qed.

Lemma forks_fork (s : Scopes) (w h c k : Z) :
  fork_of (afterStep s (Step_Forks w h c)) k = ite (k = c) (Some (Fork_mk h Life_Running)) (fork_of s k).
Proof. destruct s. reflexivity. Qed.

Lemma finish_scope (s : Scopes) (t : Z) : scope_of (afterStep s (Step_Finish t)) = scope_of s.
Proof. destruct s as [sc fk ck]. cbn. reflexivity. Qed.

Lemma finish_fork (s : Scopes) (t : Z) (f : Fork) (k : Z) :
  fork_of s t = Some f ->
  fork_of (afterStep s (Step_Finish t)) k = ite (k = t) (Some (Fork_mk (scope_of f) Life_Finished)) (fork_of s k).
Proof. destruct s as [sc fk ck]. cbn. intros ->. destruct f. reflexivity. Qed.

Lemma end_fork (s : Scopes) (w h : Z) : fork_of (afterStep s (Step_End w h)) = fork_of s.
Proof. destruct s as [sc fk ck]. cbn. reflexivity. Qed.

Lemma end_scope (s : Scopes) (w h : Z) (x : Scope) (k : Z) :
  scope_of s h = Some x ->
  scope_of (afterStep s (Step_End w h)) k =
    ite (k = h) (Some (Scope_mk (owner_of x) (parent_of x) (opened_of x) True)) (scope_of s k).
Proof. destruct s as [sc fk ck]. cbn. intros ->. destruct x. reflexivity. Qed.

Lemma end_hasOpen (s : Scopes) (w h : Z) (x : Scope) (w' h' : Z) :
  scope_of s h = Some x ->
  hasOpen (afterStep s (Step_End w h)) w' h' <-> hasOpen s w' h' /\ h' <> h.
Proof.
  intro Hx. unfold hasOpen. rewrite (end_scope s w h x h' Hx). destruct (Z.eq_dec h' h) as [-> | Hne].
  - rewrite ite_true by reflexivity. split.
    + intros (y & Hy & _ & Hnot). injection Hy as <-. exfalso. apply Hnot. exact I.
    + intros [_ Hc]. contradiction.
  - rewrite ite_false by exact Hne. tauto.
Qed.

Lemma end_openedAt (s : Scopes) (w h : Z) (x : Scope) (h' : Z) :
  scope_of s h = Some x -> openedAt (afterStep s (Step_End w h)) h' = openedAt s h'.
Proof.
  intro Hx. unfold openedAt. rewrite (end_scope s w h x h' Hx). destruct (Z.eq_dec h' h) as [-> | Hne].
  - rewrite ite_true by reflexivity. rewrite Hx. reflexivity.
  - rewrite ite_false by exact Hne. reflexivity.
Qed.

(** A program's steps so far and one more that can be taken: each still could be taken when it was. *)
Lemma taken_snoc (atStart : Scopes) (taken : list Step) (e : Step) :
  (forall before e' after, tookBetween taken before e' after -> canTake (ran atStart before) e') ->
  canTake (ran atStart taken) e ->
  forall before e' after, tookBetween (taken ++ e :: nil) before e' after -> canTake (ran atStart before) e'.
Proof.
  intros Hold Hnew before e' after E. unfold tookBetween in *.
  destruct after as [| a after] using rev_ind.
  - apply app_inj_tail in E as [-> ->]. exact Hnew.
  - clear IHafter. rewrite app_comm_cons, app_assoc in E. apply app_inj_tail in E as [E _].
    exact (Hold before e' after E).
Qed.
