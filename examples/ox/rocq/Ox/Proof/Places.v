(** Where each thread is among the scopes, and what the steps of a program keep of it.

    The system of scopes (`examples/ox/src/main/scala/scopes`, generated into `FrFlowGen.OxScopes`) says what a
    step needs. A thread that takes one knows only its own place: what it is (no fork, a fork of a scope, a fork
    past its body) and the scopes it has open, innermost first. `agrees` says that the places the threads hold
    are true of the scopes after the steps taken, and that each step could be taken when it was. Each lemma
    `agrees_…` is one kind of step: from the place of the thread that takes it, the step can be taken, and the
    places, with that thread's changed, agree with the scopes after it.

    A scope is named by the place of its herd's set of threads, a thread by its number. *)

From Stdlib Require Import ZArith List Lia Sorted.
From stdpp Require Import gmap.
From FrFlow.Jvm Require Import Machine.
From FrFlow.Scala Require Import Tree Value.
Require Import FrFlowGen.OxScopes.Domain Proofs.OxScopes.Lemmas.

Inductive role := Root | ForkIn (q : nat) | Past.
Definition place : Type := role * list nat.

(** No scope, no fork. *)
Definition none : Scopes := Scopes_mk (fun _ => None) (fun _ => None) 0.

Definition zs (q : nat) : Z := Z.of_nat q.
Definition zt (t : nat) : Z := Z.of_nat t.

Definition role_ok (s : Scopes) (w : nat) (r : role) : Prop :=
  match r with
  | Root => fork_of s (zt w) = None
  | ForkIn q => fork_of s (zt w) = Some (Fork_mk (zs q) Life_Running)
  | Past => exists h, fork_of s (zt w) = Some (Fork_mk h Life_Finished)
  end.

Definition later_first (s : Scopes) (a b : nat) : Prop := openedAt s (zs b) < openedAt s (zs a).

Definition stack_ok (s : Scopes) (w : nat) (stack : list nat) : Prop :=
  (forall h, hasOpen s (zt w) h <-> exists q, h = zs q /\ In q stack) /\ StronglySorted (later_first s) stack.

Record agrees (taken : list Step) (places : gmap nat place) (herds : gset nat) : Prop := Agrees {
  a_valid : forall before e after, tookBetween taken before e after -> canTake (ran none before) e;
  a_role : forall w r stack, places !! w = Some (r, stack) -> role_ok (ran none taken) w r;
  a_stack : forall w r stack, places !! w = Some (r, stack) -> stack_ok (ran none taken) w stack;
  a_known : forall c,
    (fork_of (ran none taken) c <> None \/ exists h x, scope_of (ran none taken) h = Some x /\ owner_of x = c) ->
    exists w, c = zt w /\ is_Some (places !! w);
  a_herds : forall h, scope_of (ran none taken) h <> None -> exists q, h = zs q /\ q ∈ herds }.

(** A herd's set holds every fork of its scope that is not past its body. *)
Definition set_ok (taken : list Step) (q : nat) (held : list val) : Prop :=
  forall t : nat, runsIn (ran none taken) (zt t) (zs q) -> In (VTid t : val) held.

Lemma agrees_sound taken places herds : agrees taken places herds -> sound (ran none taken).
Proof.
  intros [Hv _ _ _ _]. apply (sound_prefix none taken none_is_sound Hv taken nil). by rewrite app_nil_r.
Qed.

Lemma agrees_start (main : nat) : agrees nil {[main := (Root, nil)]} ∅.
Proof.
  split.
  - apply no_step_taken.
  - intros w r stack [<- [= <- <-]]%lookup_singleton_Some. reflexivity.
  - intros w r stack [<- [= <- <-]]%lookup_singleton_Some. split; [| constructor].
    intros h. split; [intros (x & Hx & _); discriminate | intros (q & _ & [])].
  - intros c [H | (h & x & Hx & _)]; [by destruct H | discriminate].
  - intros h H. by destruct H.
Qed.

Lemma sorted_same (s s' : Scopes) (stack : list nat) :
  (forall a, In a stack -> openedAt s' (zs a) = openedAt s (zs a)) ->
  StronglySorted (later_first s) stack -> StronglySorted (later_first s') stack.
Proof.
  intros Hsame Hs. induction Hs as [| a l Hs IH Hall]; constructor.
  - apply IH. intros b Hb. apply Hsame. by right.
  - rewrite Forall_forall in Hall |- *. intros b Hb. unfold later_first.
    rewrite (Hsame a (or_introl eq_refl)), (Hsame b (or_intror Hb)). by apply Hall.
Qed.

(** ** A scope opened *)

Definition opened_inside (r : role) (stack : list nat) : option Z :=
  match stack with
  | q :: _ => Some (zs q)
  | nil => match r with ForkIn h => Some (zs h) | _ => None end
  end.

Lemma agrees_open taken places herds w r stack q :
  agrees taken places herds -> places !! w = Some (r, stack) -> r <> Past -> q ∉ herds ->
  let e := Step_Open (zt w) (zs q) (opened_inside r stack) in
  agrees (taken ++ e :: nil) (<[w := (r, q :: stack)]> places) ({[q]} ∪ herds) /\
  set_ok (taken ++ e :: nil) q nil /\
  (forall q' held, set_ok taken q' held -> set_ok (taken ++ e :: nil) q' held).
Proof.
  intros Ha Hw Hr Hq e. pose proof (agrees_sound _ _ _ Ha) as Hsound.
  destruct Ha as [Hv Hrole Hstack Hknown Hherds]. set (s := ran none taken) in *.
  assert (scope_of s (zs q) = None) as Hfresh.
  { apply eq_None_not_Some. intros [x E].
    destruct (Hherds (zs q)) as (q' & Eq & Hin); [by rewrite E |]. apply Nat2Z.inj in Eq as <-. done. }
  pose proof (Hrole w r stack Hw) as Hrw. destruct (Hstack w r stack Hw) as [Hopen Hsorted].
  assert (canTake s e) as Hcan.
  { unfold e, canTake. rewrite Hfresh. repeat split.
    - intros f Hf. destruct r; unfold role_ok in Hrw; [by rewrite Hrw in Hf | | done].
      rewrite Hrw in Hf. by injection Hf as <-.
    - destruct stack as [| q0 stack].
      + assert (hasNoneOpen s (zt w)) as Hnone.
        { intros h Hh. apply Hopen in Hh as (? & _ & []). }
        destruct r; unfold role_ok in Hrw; unfold opened_inside, opensInside; [| | done].
        * split; [exact Hnone |]. intros h (f & Hf & _). by rewrite Hrw in Hf.
        * right. split; [exact Hnone |]. eexists. split; [exact Hrw | done].
      + unfold opened_inside, opensInside. left. split.
        * apply Hopen. exists q0. split; [done | by left].
        * intros other Ho. apply Hopen in Ho as (q1 & -> & [<- | Hin]); [lia |].
          apply StronglySorted_inv in Hsorted as [_ Hall]. rewrite Forall_forall in Hall.
          specialize (Hall q1 Hin). unfold later_first in Hall. lia. }
  set (s' := afterStep s e). assert (ran none (taken ++ e :: nil) = s') as Eran by apply ran_snoc.
  assert (forall w' h, hasOpen s' (zt w') h <-> (w' = w /\ h = zs q) \/ hasOpen s (zt w') h) as Hopen'.
  { intros w' h. unfold s', e. rewrite open_hasOpen by exact Hfresh. split.
    - intros [[E ->] | H]; [left; split; [by apply Nat2Z.inj | done] | by right].
    - intros [[-> ->] | H]; [by left | by right]. }
  assert (forall a, scope_of s (zs a) <> None -> openedAt s' (zs a) = openedAt s (zs a)) as Hsame.
  { intros a Ha. unfold s', e. rewrite open_openedAt. rewrite ite_false; [done |].
    intros E. apply Nat2Z.inj in E as ->. by rewrite Hfresh in Ha. }
  assert (forall w' st a, stack_ok s w' st -> In a st -> scope_of s (zs a) <> None) as Hexists.
  { intros w' st a [Ho _] Hin. destruct (proj2 (Ho (zs a))) as (x & Hx & _); [by exists a |]. by rewrite Hx. }
  split; [split | split; unfold set_ok]; rewrite ?Eran.
  - apply taken_snoc; [exact Hv | exact Hcan].
  - intros w' r' stack' Hw'. unfold role_ok, s', e. rewrite open_fork.
    destruct (PeanoNat.Nat.eq_dec w' w) as [-> | Hne].
    + rewrite lookup_insert_eq in Hw'. assert (r' = r /\ stack' = q :: stack) as [-> ->] by (by simplify_eq). exact Hrw.
    + rewrite lookup_insert_ne in Hw' by done. exact (Hrole w' r' stack' Hw').
  - intros w' r' stack' Hw'. destruct (PeanoNat.Nat.eq_dec w' w) as [-> | Hne].
    + rewrite lookup_insert_eq in Hw'. assert (r' = r /\ stack' = q :: stack) as [-> ->] by (by simplify_eq). split.
      * intros h. rewrite Hopen'. rewrite Hopen. split.
        -- intros [[_ ->] | (q1 & -> & Hin)]; [exists q; split; [done | by left] | exists q1; split; [done | by right]].
        -- intros (q1 & -> & [<- | Hin]); [by left | right; by exists q1].
      * constructor.
        -- apply (sorted_same s); [| exact Hsorted]. intros a Hin. apply Hsame.
           by apply (Hexists w stack a).
        -- rewrite Forall_forall. intros b Hb. unfold later_first.
           rewrite (Hsame b) by (by apply (Hexists w stack b)).
           unfold s', e. rewrite open_openedAt, ite_true by done.
           destruct Hsound as (_ & Hclock). unfold openedAt.
           destruct (@scope_of Scopes Scopes_has_scope s (zs b)) as [x |] eqn:Ex; [exact (Hclock _ x Ex) | by apply (Hexists w stack b) in Hb].
    + rewrite lookup_insert_ne in Hw' by done. destruct (Hstack w' r' stack' Hw') as [Ho Hs]. split.
      * intros h. rewrite Hopen'. rewrite <- Ho. split; [intros [[E _] | H]; [done | done] | by right].
      * apply (sorted_same s); [| exact Hs]. intros a Hin. apply Hsame.
        by apply (Hexists w' stack' a).
  - intros c Hc. assert (c = zt w \/ exists w', c = zt w' /\ is_Some (places !! w')) as [-> | (w' & -> & Hsome)].
    { destruct Hc as [Hf | (h & x & Hx & Ho)].
      - right. apply Hknown. left. unfold s', e in Hf. by rewrite open_fork in Hf.
      - unfold s', e in Hx. rewrite open_scope in Hx. destruct (Z.eq_dec h (zs q)) as [-> | Hne].
        + rewrite ite_true in Hx by done. injection Hx as <-. left. by rewrite <- Ho.
        + rewrite ite_false in Hx by done. right. apply Hknown. right. by exists h, x. }
    + exists w. split; [done |]. rewrite lookup_insert_eq. eauto.
    + exists w'. split; [done |]. destruct (PeanoNat.Nat.eq_dec w' w) as [-> | Hne].
      * rewrite lookup_insert_eq. eauto.
      * by rewrite lookup_insert_ne.
  - intros h Hh. unfold s', e in Hh. rewrite open_scope in Hh. destruct (Z.eq_dec h (zs q)) as [-> | Hne].
    + exists q. split; [done | set_solver].
    + rewrite ite_false in Hh by done. destruct (Hherds h Hh) as (q' & -> & Hin). exists q'. split; [done | set_solver].
  - intros t (f & Hf & Hsc & _). exfalso. unfold s', e in Hf. rewrite open_fork in Hf.
    destruct Hsound as ((_ & Hforks) & _). apply (Hforks (zt t) (zs q)); [by exists f | exact Hfresh].
  - intros q' held Hset t (f & Hf & Hrun). apply Hset. unfold s', e in Hf. rewrite open_fork in Hf. by exists f.
Qed.
