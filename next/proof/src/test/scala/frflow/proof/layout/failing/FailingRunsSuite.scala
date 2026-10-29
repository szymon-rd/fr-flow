package frflow.proof.layout.failing

import frflow.core.name.DefName
import frflow.core.ty.Ty
import frflow.proof.layout.Laid
import frflow.proof.lean.ast.LeanModule
import frflow.proof.lean.print.Print
import frflow.proof.terms.Commutation

/** A program's error as Lean states it (`Failing`): its run on `ExceptT E (StateM World)` from a world holding the
  * faults, a failing model's calls failing on them with its error, a run's post of the runs that succeed and its
  * failure clause of the others; and `impl` resting on a part about its own Definition, the code put in it
  * (`OwnParts`).
  */
class FailingRunsSuite extends munit.FunSuite:
  private lazy val failing = Laid(Failing.resolved, Map.empty, Nil)
  private def text(laid: Laid, name: String): String = Print.module(laid.modules.find(_.name.dotted ==
    s"FrFlowGen.Test.$name").getOrElse(fail(s"no module $name")): LeanModule)

  test("a program that may fail: its run through FrFlow.runOnE, typed by what a run ends in") {
    assert(text(failing, "Domain.Def_fileIt_run").contains(
      "def fileIt_run : Booking → World → ((Except String Unit) × World) :=\n" +
        "  fun (b : Booking) (w : World) => (FrFlow.runOnE (ε := String) (Test.fileIt b) w)"),
      text(failing, "Domain.Def_fileIt_run"))
    assert(text(failing, "Domain.Def_checkIt").contains("[MonadExceptOf String m]"))
  }

  test("the world holds the faults, and the shelf on ExceptT String fails on them with its error") {
    val models = text(failing, "Models")
    assert(models.contains("structure World where\n  shelved : (List Booking)\n  faults : (List Bool)"), models)
    assert(models.contains("instance : Shelved.Ops (ExceptT String (StateM World)) where\n  put b := FrFlow.failing " +
      "(fun w => w.faults) (fun w s => { w with faults := s }) \"down\" (FrFlow.within"), models)
    assert(models.contains("theorem Shelved.Ops.put_onWorldE (b : Booking) :"), models)
  }

  test("a run's post is of the runs that succeed, its failure clause of those that fail") {
    val spec = text(failing, "fileRuns.Spec")
    assert(spec.contains("(match (file b before) with | (Except.ok r, after) => (after.shelved = (b :: before.shelved))" +
      " | _ => True) ∧ (match (file b before) with | (Except.error error, after) => ((error = \"down\") ∧ " +
      "(after.shelved = before.shelved)) | _ => True)"), spec)
    assert(text(failing, "checkRuns.Spec").contains(
      "| (Except.error error, after) => (after.shelved = before.shelved) | _ => True"), text(failing, "checkRuns.Spec"))
  }

  test("commute_ reads the program's error from its type") {
    val v = Failing.resolved.theory.vocabulary
    assertEquals(v.define(DefName("fileBoth")).toList.flatMap(Commutation.of(v, _)).map(_.error), List(Some(Ty.Str)))
  }

  test("impl rests on every part, a part about the node's own Definition too, the code put in it") {
    assert(text(Laid(OwnParts.resolved, Map.empty, Nil), "totalTwo.Spec").contains(
      "∀ (h_totalCons : (Test.totalCons.claim Test.sumOf)), (Test.totalTwo.claim Test.sumOf)"))
  }
