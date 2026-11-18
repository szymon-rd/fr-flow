(** A statement's parts hold of the execution in which nothing happens.

    A step proven by hand is asked for a world that meets its parts, so that the proof does not rest on a
    contradiction. Parts that say what follows an event hold of the execution with no event (`nothing_runs`: it is
    one of any code). `frflow_feasible` gives that execution, and for each other word of the model a value that says
    nothing (no relation holds, every value is `null`), and closes each part by an event it supposes: there is
    none. A part that needs more (some event that does happen) is left to the proof file. *)

From FrFlow Require Import Base Executions.
From Stdlib Require Import ZArith.
Require Import FrFlow.Rules.Walk.

Ltac frflow_rest_witness :=
  hnf; repeat lazymatch goal with
  | |- exists _ : Z -> Event, _ => exists (fun _ => Event_Stutter)
  | |- exists _ : _, _ =>
      unshelve eexists; [intros; first [exact False | exact Value_Null | exact 0%Z | exact Event_Stutter] |]
  end.

(** Some event the hypothesis supposes of the execution: at rest there is none. *)
Ltac frflow_rest_break H :=
  lazymatch type of H with
  | _ /\ _ => let A := fresh in let B := fresh in
      destruct H as [A B]; first [frflow_rest_break A | frflow_rest_break B]
  | _ \/ _ => destruct H as [H | H]; frflow_rest_break H
  | exists _, _ => let x := fresh in destruct H as [x H]; frflow_rest_break H
  | Event_Stutter = _ => discriminate H
  | _ = Event_Stutter => discriminate H
  | False => destruct H
  end.

(** A part: some event it supposes, or what it supposes contradicts itself as it stands (a flag set and not set). *)
Ltac frflow_rest_part :=
  repeat (hnf; first [progress intros | split]);
  first
  [ solve [ match goal with H : _ |- _ => autounfold with frflow_defs in H; cbv beta in H; frflow_rest_break H end ]
  | solve [ repeat match goal with H : _ |- _ => progress (autounfold with frflow_defs in H; cbv beta in H) end;
            tauto ] ].

Ltac frflow_at_rest :=
  frflow_rest_witness; first [split; [apply nothing_runs |] | idtac]; repeat split; frflow_rest_part.

(** What FrFlow tries of a `feasible` no proof file gives: the execution at rest, or nothing (the automation for
    statements about values finds no execution, and runs out of memory looking). *)
Ltac frflow_feasible := solve [frflow_at_rest].
