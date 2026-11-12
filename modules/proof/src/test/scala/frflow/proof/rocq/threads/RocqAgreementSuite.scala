package frflow.proof.rocq.threads

import frflow.core.threads.{Ctor, Decl, Param, Program, Section, Term, Ty}

/** The file that states a generated file agrees with one written by hand. */
class RocqAgreementSuite extends munit.FunSuite:
  private val scope = Decl.Inductive("Scope", List(Ctor("mkScope", List(Param("id", Ty.Nat),
    Param("parent", Ty.option(Ty.Named("Scope")))))))
  private val open: Decl.Definition = Decl.Definition("open", List(Param("f", Ty.Code), Param("x1", Ty.Named("Scope"))),
    Decl.M(Ty.Val), Term.of("invoke", Term.Ref("f"), Term.Ref("VUnit")))
  private val program = Program(List(scope), Nil, Nil, Nil, List(Section("s", List(open))), Ty.Named("Scope"))

  test("each type has a function to the hand-written file's and back, a constructor to its namesake") {
    val file = RocqAgreement.file(program, "U.Code", "U.Gen", Map.empty)
    val parent = "(match a2 with Some y => Some (to_code_Scope y) | None => None end)"
    assert(file.contains(
      s"""Fixpoint to_code_Scope (x : U.Gen.Scope) : U.Code.Scope :=
         |  match x with
         |  | U.Gen.mkScope a1 a2 => U.Code.mkScope a1 $parent
         |  end.""".stripMargin), file)
    assert(file.contains("Fixpoint of_code_Scope (x : U.Code.Scope) : U.Gen.Scope :="), file)
    assert(file.contains("| U.Gen.Client a1 a2 => U.Code.Client a1 (List.map (fun y => (to_code_Scope y)) a2)"), file)
  }

  test("each definition is stated equal to the hand-written one of its name, and interp too") {
    val file = RocqAgreement.file(program, "U.Code", "U.Gen", Map.empty)
    assert(file.contains("Require Import U.Code.\nRequire U.Gen."), file)
    val over = file.substring(file.indexOf("Module Over."), file.indexOf("End Over."))
    assert(over.contains("Definition open (f : code) (x1 : Scope) : M val := invoke f VUnit."), over)
    assert(over.contains("Section Interp."), over)
    assert(file.contains("Lemma open_agrees : @Over.open = @U.Code.open. Proof. reflexivity. Qed."), file)
    assert(file.contains("Lemma interp_agrees : @Over.interp = @U.Code.interp. Proof. reflexivity. Qed."), file)
  }

  test("a definition the hand-written file takes in another order is stated equal once taken in that order") {
    val file = RocqAgreement.file(program, "U.Code", "U.Gen", Map("open" -> List("x1", "f")))
    assert(file.contains(
      "Lemma open_agrees : (fun x1 f => @Over.open f x1) = @U.Code.open. Proof. reflexivity. Qed."), file)
  }
