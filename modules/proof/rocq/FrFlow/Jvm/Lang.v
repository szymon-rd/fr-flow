(** The machine's threads as a language of Iris (https://iris-project.org): what its program logic, its
    invariants and its adequacy theorem are about.

    An expression is a thread, running or ended; a thread that has ended is a value. One step is `Machine.step`.
    Nothing is observed. *)

From iris.program_logic Require Export language.
From FrFlow.Threads Require Import Prog.
From FrFlow.Jvm Require Export Machine.

Section lang.
  Context {code obj : Type} (interp : code → Machine.val code obj → Machine.P code obj (Machine.res code obj)).

  Definition final : Type := tid * Machine.res code obj.

  Definition of_final (v : final) : running code obj := Ended v.1 v.2.

  Definition to_final (e : running code obj) : option final :=
    match e with
    | Ended t r => Some (t, r)
    | Running _ _ => None
    end.

  Definition thread_step (e : running code obj) (σ : Machine.state code obj) (κ : list Empty_set)
      (e' : running code obj) (σ' : Machine.state code obj) (started : list (running code obj)) : Prop :=
    κ = [] ∧ Machine.step interp e σ e' σ' started.

  Lemma jvm_mixin : LanguageMixin of_final to_final thread_step.
  Proof.
    split.
    - by intros [t r].
    - intros [t p | t r] [t' r']; simpl; [done |]. by intros [= <- <-].
    - intros [t p | t r] σ κ e' σ' started [_ H]; [done | destruct H].
  Qed.

  Canonical Structure jvm : language := Language jvm_mixin.

End lang.
