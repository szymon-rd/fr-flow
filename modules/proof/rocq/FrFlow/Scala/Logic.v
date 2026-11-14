(** Proving a program that is the meaning of trees: the rules of the machine's logic (`FrFlow.Jvm`), said of
    programs as `Meaning.denote` gives them, and the steps a proof takes through one.

    A proof walks the program: `wp_whd` computes what the program does next (an operation, a call, a loop, its
    result) and leaves the rest as it is; a rule is applied to that; and again. The program is never computed
    whole. *)

From iris.proofmode Require Import proofmode.
From FrFlow.Threads Require Export Prog.
From FrFlow.Jvm Require Export Adequacy.
From FrFlow.Scala Require Export Tree Program Table Equal Value Meaning Jdk Library.

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

(** What the program does next, computed; the rest left as it is. *)
Ltac wp_whd :=
  lazymatch goal with
  | |- environments.envs_entails ?Δ (wpP ?i ?t ?p ?E ?Φ) =>
      let p' := eval lazy head in p in
      change (environments.envs_entails Δ (wpP i t p' E Φ))
  end.

(** The next step is an operation: the rule for it is applied next. *)
Ltac wp_op := wp_whd; iApply wpP_vis.

(** The program has ended. *)
Ltac wp_done := wp_whd; iApply wpP_ret.

(** The next step is a call of a closure: what the closure runs is proven next, a step later. *)
Ltac wp_call := wp_whd; iApply wpP_call_then; iNext.
