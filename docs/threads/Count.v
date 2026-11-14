(** Why `isEmpty` of a concurrent set can say `true` of a set that is never empty.

    `ConcurrentHashMap` does not keep its size in one place: each thread that adds or removes changes a counter
    cell of its own (so that threads do not contend), and `size` and `isEmpty` add the cells up, one after
    another, while other threads go on changing them. This is the least model of that: two cells, an element
    added on one and removed on the other, and a reader that reads the first cell, then the second.

    - `sum_is_size`: the cells always add up to the number of elements. Read at one moment, they are exact.
    - `wrong_true`: there is a run in which the set holds an element at every moment, and the reader's sum is
      zero. An element is in the set from the start. The reader reads the first cell. A thread adds a second
      element (on the first cell, which the reader has passed); that element is then removed by another thread
      (on the second cell); the reader reads the second cell. It has counted the removal and missed the addition.

    In Ox a fork is added to its scope's set by the thread that starts it and removes itself: an addition and a
    removal on different cells. The closing loop of a scope ends when `isEmpty` answers `true`.
    `examples/ox/probe/IsEmptyProbe.scala` is this run on the JDK: 44 wrong answers of 717 million. *)

From Stdlib Require Import ZArith List Lia.
Import ListNotations.
Open Scope Z_scope.

(** The set's elements counted, the two cells, and how far the reader is: it has read nothing, or the first
    cell (and holds what it read), or both (and holds their sum). *)
Inductive reader := Idle | ReadFirst (seen : Z) | Summed (sum : Z).
Record state := State { size : Z; first : Z; second : Z; at_ : reader }.

Inductive step : state -> state -> Prop :=
  (* an element added or removed, counted on the first cell or on the second *)
  | add_first n a b r : step (State n a b r) (State (n + 1) (a + 1) b r)
  | add_second n a b r : step (State n a b r) (State (n + 1) a (b + 1) r)
  | remove_first n a b r : 0 < n -> step (State n a b r) (State (n - 1) (a - 1) b r)
  | remove_second n a b r : 0 < n -> step (State n a b r) (State (n - 1) a (b - 1) r)
  (* the reader: the first cell, then the second *)
  | read_first n a b : step (State n a b Idle) (State n a b (ReadFirst a))
  | read_second n a b seen : step (State n a b (ReadFirst seen)) (State n a b (Summed (seen + b))).

Inductive run : state -> list state -> state -> Prop :=
  | run_none s : run s [] s
  | run_more s mid s' s'' : run s mid s' -> step s' s'' -> run s (mid ++ [s']) s''.

(** The cells add up to the size, whatever the threads do. *)
Lemma sum_is_size s mid s' : first s + second s = size s -> run s mid s' -> first s' + second s' = size s'.
Proof.
  intros H0 Hr. induction Hr as [| s mid s' s'' _ IH Hs]; trivial.
  specialize (IH H0). destruct Hs; cbn in *; lia.
Qed.

(** One element, counted on the first cell; the reader has not begun. *)
Definition start : state := State 1 1 0 Idle.

(** A run in which the set is never empty, and the reader's sum is zero. *)
Theorem wrong_true :
  exists mid last, run start mid last /\ at_ last = Summed 0 /\ Forall (fun s => 0 < size s) (mid ++ [last]).
Proof.
  exists [start; State 1 1 0 (ReadFirst 1); State 2 2 0 (ReadFirst 1); State 1 2 (-1) (ReadFirst 1)].
  exists (State 1 2 (-1) (Summed 0)). split; [| split].
  - change [start; State 1 1 0 (ReadFirst 1); State 2 2 0 (ReadFirst 1); State 1 2 (-1) (ReadFirst 1)]
      with ((([] ++ [start]) ++ [State 1 1 0 (ReadFirst 1)]) ++ [State 2 2 0 (ReadFirst 1)]
              ++ [State 1 2 (-1) (ReadFirst 1)]).
    rewrite app_assoc.
    eapply run_more; [eapply run_more; [eapply run_more; [eapply run_more; [apply run_none |] |] |] |].
    + apply read_first.
    + exact (add_first 1 1 0 (ReadFirst 1)).
    + exact (remove_second 2 2 0 (ReadFirst 1) ltac:(lia)).
    + exact (read_second 1 2 (-1) 1).
  - reflexivity.
  - repeat constructor; cbn; lia.
Qed.

(** Read with no step between, the sum is the size: the answer is wrong only when the set changes meanwhile. *)
Lemma right_when_quiet n a b : a + b = n ->
  exists s1 s2, step (State n a b Idle) s1 /\ step s1 s2 /\ at_ s2 = Summed n.
Proof.
  intro H. exists (State n a b (ReadFirst a)), (State n a b (Summed (a + b))).
  repeat split; [apply read_first | apply read_second | cbn; f_equal; exact H].
Qed.
