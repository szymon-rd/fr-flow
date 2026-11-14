(** What the proofs about Ox are about: the meaning of Ox's trees, in a program that may define more.

    `Ox` is the table of Ox's 116 files. A program that uses Ox is Ox's definitions and then its own
    (`Table.extend`); `run more` is what a closure of such a program runs. A lemma here is about `run more` for
    every `more`: it holds of Ox in every program. *)

From FrFlow.Scala Require Export Logic.
Require Export Ox.Tree.All.

Definition Ox : table := Eval vm_compute in build files.

(** What a closure runs, in a program that defines `more` after Ox. *)
Definition run (more : table) : code → val → Machine.P code obj (Machine.res code obj) :=
  Meaning.interp (extend Ox more) Library.outside Library.supers.
