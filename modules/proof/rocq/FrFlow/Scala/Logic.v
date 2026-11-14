(** Proving a program that is the meaning of trees: the rules of the machine's logic (`FrFlow.Jvm`), said of
    programs as `Meaning.denote` gives them, and the steps a proof takes through one.

    A proof walks the program: `wp_whd` computes what the program does next (an operation, a call, a loop, its
    result) and leaves the rest as it is; a rule is applied to that; and again. The program is never computed
    whole. *)

From iris.proofmode Require Import proofmode.
From FrFlow.Threads Require Export Prog.
From FrFlow.Jvm Require Export Adequacy.
From FrFlow.Scala Require Export Tree Program Table Equal Value Meaning Jdk Library Collections.

Section logic.
  Context `{!jvmGS code obj Σ}.
  Context (I : code → val → Machine.P code obj (Machine.res code obj)).
  Local Instance logic_irisGS : irisGS (jvm I) Σ := jvm_irisGS I.

  Abbreviation prog := (Machine.P code obj).

  (** An operation, then what follows it. *)
  Lemma wpP_vis {A X} t (o : Machine.op code obj X) (k : X → prog A) E Φ :
    wpP I t (Vis o Ret) E (λ x, wpP I t (k x) E Φ) ⊢ wpP I t (Vis o k) E Φ.
  Proof. iIntros "H". by iApply (wpP_bind I t (Vis o Ret) k). Qed.

  (** A call of a closure, then what follows it. *)
  Lemma wpP_call_then {A} t c arg (k : Machine.res code obj → prog A) E Φ :
    ▷ wpP I t (I c arg) E (λ r, wpP I t (k r) E Φ) ⊢ wpP I t (Call c arg k) E Φ.
  Proof.
    iIntros "H". iApply (wpP_bind I t (Call c arg Ret) k). by iApply wpP_call.
  Qed.

  (** A loop: what holds before each turn, kept by a turn that goes on, gives what follows a turn that ends. *)
  Lemma wpP_loop {S B} t (body : S → prog (S + B)) s E (J : S → iProp Σ) (Q : B → iProp Σ) :
    J s -∗
    □ (∀ s, J s -∗ wpP I t (body s) E (λ r, match r with inl s' => J s' | inr b => Q b end)) -∗
    wpP I t (Iter body s Ret) E Q.
  Proof.
    iIntros "HJ #Hbody". iLöb as "IH" forall (s). iApply wpP_iter. iNext.
    unfold unfold_iter. iApply wpP_bind. iApply (wpP_wand with "[HJ]"); [by iApply "Hbody" |].
    iIntros ([s' | b]) "H"; simpl; [by iApply "IH" | by iApply wpP_ret].
  Qed.

  Lemma wpP_loop_then {A S B} t (body : S → prog (S + B)) s (k : B → prog A) E (J : S → iProp Σ) Φ :
    J s -∗
    □ (∀ s, J s -∗ wpP I t (body s) E (λ r, match r with inl s' => J s' | inr b => wpP I t (k b) E Φ end)) -∗
    wpP I t (Iter body s k) E Φ.
  Proof.
    iIntros "HJ #Hbody". iApply (wpP_bind I t (Iter body s Ret) k). by iApply (wpP_loop with "HJ").
  Qed.

End logic.

(** ** Walking a program

    `wp_whd` computes what the program does next (an operation, a call, a loop, its result). What follows that
    is set aside under a name (`K`), a definition of the proof's context, and the goal speaks of it by name;
    the walk opens a name when the program reaches it. What follows holds the meaning of every tree not yet
    reached, as calls not yet computed, each with the variables in scope: it is large, and the tactics of
    Iris's proof mode look through the whole goal they are given. Kept under a name, it is out of their sight.

    Where the walk cannot go on because the program asks something that is not computed (whether two threads
    are the same, a value not known), it stops with the program that asks in view and what follows it under
    names; the proof answers (a rewrite, a case) and walks on. *)

(** The program that asks, with each program that waits for it set aside. *)
Ltac wp_peel q :=
  match q with
  | ?h ?q2 ?g =>
      let _ := match goal with _ => unify (h q2 g) (pbind q2 g) end in
      let G := fresh "K" in
      let _ := match goal with _ => pose (G := g) end in
      let q2' := wp_peel q2 in
      constr:(pbind q2' G)
  | _ => q
  end.

Ltac wp_seal := idtac.

Ltac wp_shape Δ i t p E Φ :=
  lazymatch p with
  | Ret ?a => change (environments.envs_entails Δ (wpP i t (Ret a) E Φ))
  | Vis ?o ?k =>
      let K := fresh "K" in
      pose (K := k); change (environments.envs_entails Δ (wpP i t (Vis o K) E Φ)); wp_seal
  | Call ?c ?a ?k =>
      let K := fresh "K" in
      pose (K := k); change (environments.envs_entails Δ (wpP i t (Call c a K) E Φ)); wp_seal
  | Iter ?b ?s ?k =>
      let B := fresh "B" in
      let K := fresh "K" in
      pose (B := b); pose (K := k); change (environments.envs_entails Δ (wpP i t (Iter B s K) E Φ)); wp_seal
  | _ =>
      let q := wp_peel p in
      change (environments.envs_entails Δ (wpP i t q E Φ)); wp_seal
  end.

(** A name the program has reached is opened; a name nothing speaks of any more is dropped. *)
Ltac wp_walk Δ i t p E Φ :=
  let p' := eval lazy head in p in
  wp_shape Δ i t p' E Φ;
  repeat match goal with K := _ |- _ => clear K end.

Ltac wp_whd :=
  lazymatch goal with
  | |- environments.envs_entails ?Δ (wpP ?i ?t ?p ?E ?Φ) => wp_walk Δ i t p E Φ
  | |- environments.envs_entails ?Δ (?F ?a) =>
      (* what was set aside, given the result of the program it waited for *)
      let G := eval cbv beta head in (F a) in
      lazymatch G with
      | wpP ?i ?t ?p ?E ?Φ => wp_walk Δ i t p E Φ
      end
  end.

(** Where the walk has stopped at a program that a lemma is about (an object named, say): the goal is that
    program's, with what follows it as what it must give. *)
Ltac wp_leaf :=
  repeat lazymatch goal with
  | |- environments.envs_entails _ (wpP _ _ (pbind _ _) _ _) => iApply wpP_bind
  end.

(** The next step is an operation: the rule for it is applied next. *)
Ltac wp_op := wp_whd; iApply wpP_vis.

(** The program has ended. *)
Ltac wp_done := wp_whd; iApply wpP_ret.

(** The next step is a call of a closure: what the closure runs is proven next, a step later. *)
Ltac wp_call := wp_whd; iApply wpP_call_then; iNext.

(** A field of an object: read of one the thread holds (`H` names what holds it), read of one that no longer
    changes, and written. *)
Tactic Notation "wp_get" constr(H) :=
  wp_op; iApply wp_obj_get; iModIntro; iExists _, _, _, _; iFrame H;
  iSplit; [iPureIntro; split; reflexivity |]; iIntros "!>"; iIntros H; iModIntro.
Tactic Notation "wp_read" constr(H) :=
  wp_op; iApply wp_obj_get; iModIntro; iExists _, _, _, _; iFrame H;
  iSplit; [iPureIntro; split; reflexivity |]; iIntros "!> _ !>".
(** A field that is not volatile, written: marked, then the value stored (`Machine.writing`). *)
Tactic Notation "wp_set" constr(H) :=
  wp_op; iApply wp_obj_mark; iModIntro; iExists _, _; iFrame H;
  iSplit; [iPureIntro; reflexivity |]; iIntros "!>"; iIntros H; iModIntro;
  wp_op; iApply wp_obj_set; iModIntro; iExists _, _; iFrame H;
  iSplit; [iPureIntro; by cbn |]; iIntros "!>"; iIntros H; iModIntro;
  iEval (cbn) in H.
(** A field written in one step: a volatile field, or what a lazy value or a class's initialisation sets. *)
Tactic Notation "wp_put" constr(H) :=
  wp_op; iApply wp_obj_set; iModIntro; iExists _, _; iFrame H;
  iSplit; [iPureIntro; by cbn |]; iIntros "!>"; iIntros H; iModIntro;
  iEval (cbn) in H.

(** What the program does next, shown: for finding the way through a program. *)
Ltac wp_peek := wp_whd; lazymatch goal with |- environments.envs_entails _ (wpP _ _ ?p _ _) =>
  lazymatch p with
  | Vis ?o _ => idtac "op:" o
  | Call (Method ?s) ?a _ => idtac "call method:" s a
  | Call (Init ?s) ?a _ => idtac "call init:" s a
  | Call (Fn _ _ _) ?a _ => idtac "call fn:" a
  | Call (Thunk _ _) ?a _ => idtac "call thunk:" a
  | Call (Bound ?s ?v) ?a _ => idtac "call bound:" s v a
  | Iter _ ?s _ => idtac "iter:" s
  | Ret ?a => idtac "ret:" a
  | _ => idtac "stopped at a question"
  end end.

(** Whether two values, two threads or two places are the same is not computed while a program is walked: the
    walk stops at the question, and the proof answers it (`val_eqb_refl`, `val_eqb_other`, `same_place_refl`,
    `same_place_other`). *)
Lemma val_eqb_other (a b : val) : a ≠ b → val_eqb a b = false.
Proof. intros H. unfold val_eqb. by destruct (val_eq_dec a b). Qed.

Global Opaque val_eqb same_place has_thread of_thread.
