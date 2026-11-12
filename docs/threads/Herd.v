(** A model of the thread set behind an Ox scope (`ox.internal.ThreadHerd`, Ox 1.1.0), for docs/THREADS.md.

    It keeps what decides whether a scope's forks have finished when the scope completes: the set `threads`, the
    flag `shutdownInProgress`, each fork's life, where the scope's owner is, and where each caller of `startThread`
    is between its check of the flag, its `threads.add` and its `thread.start`. Each of those is one step, and the
    steps of different threads interleave in any order. `interrupt` and `join` change none of this, so they are not
    steps of the model: the closing loop ends when it finds the set empty.

    What is assumed of the JVM is what the steps say: `add`, `remove` and `isEmpty` on the set are each one step;
    a thread started runs its body once and takes itself out of the set as its last step; a caller of
    `startThread` does not end between its three steps.

    Checked with Rocq 9.3 and its standard library: `rocq compile docs/threads/Herd.v`. *)

From Stdlib Require Import Arith.

Inductive status := New | Running | Done.
Inductive ownerpc := Body | Closing | Exited.

(** Who may call `startThread`: the scope's owner, a fork of the scope, or a thread that is neither and was handed
    the scope's capability. *)
Inductive who := Owner | Fork (t : nat) | Outsider.

(** Where a caller is in `startThread`: outside it, past `assertNotShuttingDown`, or past `threads.add(c)`. *)
Inductive starting := Idle | Checked | Added (c : nat).

Definition who_dec (a b : who) : {a = b} + {a <> b}.
Proof. decide equality. apply Nat.eq_dec. Defined.

Definition upd {A B : Type} (dec : forall a b : A, {a = b} + {a <> b}) (f : A -> B) (k : A) (v : B) : A -> B :=
  fun x => if dec x k then v else f x.

Record state := State {
  member : nat -> bool;     (* the set `threads` *)
  st : nat -> status;       (* each fork: not started, running its body, finished *)
  shutdown : bool;          (* `shutdownInProgress` *)
  pc : ownerpc;             (* the owner: in the scope's body, in the closing loop, past it *)
  call : who -> starting }.

Definition init := State (fun _ => false) (fun _ => New) false Body (fun _ => Idle).

Section Scope.

(** Whether the scope's capability stays with the owner and the scope's forks. *)
Variable confined : Prop.

Definition active (s : state) (w : who) : Prop :=
  match w with
  | Owner => pc s = Body
  | Fork t => st s t = Running
  | Outsider => ~ confined
  end.

Inductive step : state -> state -> Prop :=
  | s_check s w : active s w -> call s w = Idle -> shutdown s = false ->
      step s (State (member s) (st s) (shutdown s) (pc s) (upd who_dec (call s) w Checked))
  | s_add s w c : active s w -> call s w = Checked -> st s c = New -> member s c = false ->
      step s (State (upd Nat.eq_dec (member s) c true) (st s) (shutdown s) (pc s)
        (upd who_dec (call s) w (Added c)))
  | s_run s w c : active s w -> call s w = Added c ->
      step s (State (member s) (upd Nat.eq_dec (st s) c Running) (shutdown s) (pc s)
        (upd who_dec (call s) w Idle))
  | s_finish s t : st s t = Running -> call s (Fork t) = Idle ->
      step s (State (upd Nat.eq_dec (member s) t false) (upd Nat.eq_dec (st s) t Done) (shutdown s) (pc s)
        (call s))
  | s_close s : pc s = Body -> call s Owner = Idle ->
      step s (State (member s) (st s) true Closing (call s))
  | s_exit s : pc s = Closing -> (forall t, member s t = false) ->
      step s (State (member s) (st s) (shutdown s) Exited (call s)).

Inductive reachable : state -> Prop :=
  | r_init : reachable init
  | r_step s s' : reachable s -> step s s' -> reachable s'.

(** What every step keeps, when the capability is confined. *)
Definition inv (s : state) : Prop :=
  (forall t, st s t = Running -> member s t = true) /\
  (forall w, call s w <> Idle -> active s w) /\
  (forall w c, call s w = Added c -> member s c = true /\ st s c = New) /\
  (forall w w' c, call s w = Added c -> call s w' = Added c -> w = w') /\
  (pc s = Exited -> forall t, member s t = false).

Ltac split_upd :=
  repeat match goal with
    | H : context [upd _ _ _ _ _] |- _ => unfold upd in H
    | |- context [upd _ _ _ _ _] => unfold upd
    | H : context [if ?d then _ else _] |- _ => destruct d; subst
    | |- context [if ?d then _ else _] => destruct d; subst
    end.

(** What the invariant gives of each caller named in the hypotheses. *)
Ltac saturate H2 H3 :=
  repeat match goal with
    | H : Added _ = Added _ |- _ => injection H as H; subst
    | H : call ?s ?w = Added ?c |- _ =>
        lazymatch goal with
        | _ : member s c = true |- _ => fail
        | _ => destruct (H3 _ _ H)
        end
    | H : call ?s ?w <> Idle |- _ =>
        lazymatch goal with
        | _ : active s w |- _ => fail
        | _ => pose proof (H2 _ H)
        end
    end.

Ltac act := match goal with |- active _ ?w => destruct w; cbn in *; split_upd end.

Lemma inv_init : inv init.
Proof. repeat split; cbn; intros; try discriminate; try (elim H; reflexivity). Qed.

Lemma no_caller_after_exit s w : confined -> inv s -> pc s = Exited -> call s w = Idle.
Proof.
  intros Hc (H1 & H2 & _ & _ & H5) Hpc.
  destruct (call s w) eqn:E; trivial.
  all: assert (Ha : active s w) by (apply H2; congruence).
  all: destruct w; cbn in Ha; try congruence; try contradiction.
  all: specialize (H1 _ Ha); rewrite (H5 Hpc) in H1; discriminate.
Qed.

Lemma inv_step s s' : confined -> inv s -> step s s' -> inv s'.
Proof.
  intros Hc Hinv Hstep.
  pose proof (no_caller_after_exit s) as Hquiet.
  pose proof Hinv as (H1 & H2 & H3 & H4 & H5).
  destruct Hstep as [s w Ha Hi Hs | s w c Ha Hk Hn Hm | s w c Ha Hk | s t Hr Hi | s Hp Hi | s Hp He].
  all: repeat split; cbn; intros; cbn in *; split_upd; saturate H2 H3; try act.
  all: try discriminate; try congruence; auto.
  all: try (eapply H4; eassumption).
  all: try (exfalso; match goal with n : ?a <> ?b |- _ => apply n; eapply H4; eassumption end).
  all: match goal with H : pc ?s = Exited |- _ => pose proof (fun w => Hquiet w Hc Hinv H) as Hq end.
  all: match goal with K : call ?s ?w = Checked |- _ => specialize (Hq w); congruence end.
Qed.

Lemma inv_reachable s : confined -> reachable s -> inv s.
Proof. intros Hc Hr. induction Hr; [apply inv_init | eapply inv_step; eassumption]. Qed.

(** Containment. When the capability stays with the owner and the scope's forks, once the owner is past the closing
    loop no fork is running its body, no call of `startThread` is under way, and nothing more happens. *)
Theorem contained s : confined -> reachable s -> pc s = Exited ->
  (forall t, st s t <> Running) /\ (forall w, call s w = Idle) /\ (forall s', ~ step s s').
Proof.
  intros Hc Hr Hpc.
  pose proof (inv_reachable s Hc Hr) as Hinv.
  assert (Hquiet : forall w, call s w = Idle) by (intro w; apply no_caller_after_exit; assumption).
  destruct Hinv as (H1 & _ & _ & _ & H5).
  assert (Hrun : forall t, st s t <> Running).
  { intros t Ht. specialize (H1 _ Ht). rewrite (H5 Hpc) in H1. discriminate. }
  repeat split; trivial.
  intros s' Hstep.
  assert (Hact : forall w, ~ active s w).
  { intros [| t |]; cbn; [congruence | apply Hrun | tauto]. }
  inversion Hstep; subst; try congruence.
  all: try (eapply Hact; eassumption).
  all: try (eapply Hrun; eassumption).
  all: match goal with K : call ?s ?w = _ |- _ => specialize (Hquiet w); congruence end.
Qed.

(** The leak. When a thread that is neither the owner nor a fork holds the capability, a scope can complete with a
    fork of its own still to run: the outsider passes the check, the owner closes and finds the set empty, and
    the outsider then adds its thread and starts it. *)
Theorem leaks : ~ confined -> exists s, reachable s /\ pc s = Exited /\ st s 0 = Running.
Proof.
  intro Hn.
  eexists. split; [| split].
  - eapply r_step; [eapply r_step; [eapply r_step; [eapply r_step; [eapply r_step; [apply r_init |] |] |] |] |].
    + apply (s_check init Outsider); cbn; trivial.
    + apply s_close; cbn; trivial.
    + apply s_exit; cbn; trivial.
    + eapply (s_add _ Outsider 0); cbn; trivial.
    + eapply (s_run _ Outsider 0); cbn; trivial.
  - reflexivity.
  - reflexivity.
Qed.

End Scope.
