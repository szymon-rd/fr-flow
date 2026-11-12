package frflow.proof.rocq.threads

import frflow.core.threads.{Ctor, Decl, Param, Program, Section, Term, Ty}

/** A unit read, as a Rocq file: its declarations, and the frame around them. */
class RocqThreadsSuite extends munit.FunSuite:
  private val pair = Decl.Record("Pair", List(Param("left", Ty.Nat), Param("right", Ty.Tid)))
  private val tree = Decl.Inductive("Tree", List(Ctor("Leaf", Nil), Ctor("Node", List(Param("x", Ty.Named("Pair"))))))
  private val closure = Ctor("Lam_f_1", List(Param("this", Ty.Named("Pair")), Param("t", Ty.Code)))
  private val f: Decl.Definition =
    Decl.Definition("f", List(Param("this", Ty.Named("Pair"))), Decl.M(Ty.Unit), Term.ret(Term.unit))
  private val program = Program(List(pair, tree), List(closure), Nil, Nil, List(Section("a.Pair", List(f))),
    Ty.Named("Pair"))
  private val file = RocqThreads.file(program, "A pair.")

  test("a class is a record of its fields, each named for the class; a sum an inductive type") {
    assert(file.contains("Record Pair := mkPair {\n  Pair_left : nat;\n  Pair_right : tid }."), file)
    assert(file.contains("Inductive Tree :=\n  | Leaf\n  | Node (x : Pair)."), file)
  }

  test("code has a constructor for each closure, and Client, over the capabilities a caller's closure holds") {
    assert(file.contains(
      "Inductive code :=\n  | Lam_f_1 (this : Pair) (t : code)\n  | Client (n : nat) (caps : list Pair)."), file)
    assert(file.contains("Abbreviation val := (Jdk.val code obj).\nAbbreviation M := (Lang.M code obj)."), file)
  }

  test("interp runs each closure's definition, and the caller's by what the caller says") {
    assert(file.contains("  Variable client : nat -> list Pair -> val -> M val."), file)
    assert(file.contains("    | Lam_f_1 this t => Lam_f_1_body this t arg\n"), file)
    assert(file.contains("    | Client n caps => client n caps arg\n    end."), file)
  }

  test("a definition is written under its section's heading, on one line where it fits") {
    assert(file.contains("(** ** a.Pair *)\n\nDefinition f (this : Pair) : M unit := ret tt."), file)
    assert(file.startsWith("(** A pair. *)\n\nFrom Stdlib Require Import ZArith List Bool String."), file)
  }
