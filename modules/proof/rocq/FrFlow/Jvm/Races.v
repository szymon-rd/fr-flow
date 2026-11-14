(** A race, found by the machine: one thread writes a field of an object while another reads it.

    The writer marks the field and then stores; the reader reads. In the run where the reader's turn comes
    between the writer's two steps, the reader is at a field that is being written (`Machine.races`), and its
    step goes wrong. A proof in the logic cannot be had of this program: `jvm_race_free` would contradict
    this. *)

From Stdlib Require Import String List.
Require Import FrFlow.Threads.Prog FrFlow.Jvm.Machine.
Import ListNotations.
Open Scope string_scope.

Section example.
  Let code : Type := unit.
  Let obj : Type := unit.
  Let interp (c : code) (arg : val code obj) : P code obj (res code obj) := Ret (inr VUnit).

  Definition writes : P code obj (res code obj) :=
    Vis (ObjMark 0 "x") (fun _ => Vis (ObjSet 0 "x" (VBool true)) (fun _ => Ret (inr VUnit))).
  Definition reads : P code obj (res code obj) := Vis (ObjGet 0 "x") (fun r => Ret r).

  Definition before : state code obj :=
    State (fun _ => None) (fun r => match r with 0 => Some ("C", [("x", VBool false)]) | _ => None end)
      (fun _ => None) None.

  Lemma a_race_is_reached :
    exists c, reaches interp ([Running 0 writes; Running 1 reads], before) c /\ races c.
  Proof.
    exists ([Running 0 (Vis (ObjSet 0 "x" (VBool true)) (fun _ => Ret (inr VUnit))); Running 1 reads],
            set_obj before 0 ("C", with_field [("x", VBool false)] (writing "x") (VTid 0))).
    split.
    - eapply reaches_step; [apply reaches_refl |].
      apply (move interp [] (Running 0 writes) [Running 1 reads] before
               (Running 0 (Vis (ObjSet 0 "x" (VBool true)) (fun _ => Ret (inr VUnit)))) _ []).
      cbn. exists (inr tt). auto.
    - exists 1, _, (ObjGet 0 "x"), (fun r => Ret r). split; [right; left; reflexivity |].
      cbn. eexists _, _, 0. split; [reflexivity |]. split; [reflexivity | discriminate].
  Qed.

  (** And so a state that has gone wrong. *)
  Lemma the_race_goes_wrong :
    exists c, reaches interp ([Running 0 writes; Running 1 reads], before) c /\ s_wrong (snd c) <> None.
  Proof.
    destruct a_race_is_reached as (c & Hc & Hrace). destruct (race_goes_wrong interp Hrace) as (c' & Hm & Hw).
    exists c'. split; [eapply reaches_step; eassumption | exact Hw].
  Qed.
End example.
