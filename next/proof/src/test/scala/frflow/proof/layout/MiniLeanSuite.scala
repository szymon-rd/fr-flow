package frflow.proof.layout

import frflow.proof.lean.ast.LeanModule
import frflow.proof.lean.print.Print
import frflow.proof.obligation.{Discharge, Obligation}
import frflow.proof.reading.Elaboration
import frflow.proof.verdict.{Judge, ObligationStatus}

/** Mini's modules built by Lean (`sbt leanTest`): every module but a node's checks builds; every obligation FrFlow's
  * automation or witnesses are to meet is proven, as the judges read Lean's output; the only errors are tries Lean
  * did not prove (one-sided: they show nothing).
  */
class MiniLeanSuite extends munit.FunSuite:
  override val munitTimeout: scala.concurrent.duration.Duration = scala.concurrent.duration.Duration(20, "minutes")

  private lazy val built: (LeanWorkspace, String) =
    val w = LeanWorkspace.make("mini")
    (w, w.build(MiniProject.modules)._2)

  private def elaboration(m: LeanModule): Elaboration =
    Elaboration(Print.module(m), built._2, m.name.file.value.stripPrefix("lean/"))

  private def obligations: List[Obligation] =
    MiniProject.nodes.flatMap(o => o.required ++ o.tried) ++ MiniProject.whole

  test("every required obligation is proven: complete, impl, cover_, consistent_, start_, inhabited_".tag(LeanTag)) {
    val required = obligations.filter(o => o.discharge == Discharge.Auto || o.discharge.isInstanceOf[Discharge.Witnessed])
    val results = for
      m <- MiniProject.modules
      e = elaboration(m)
      o <- required if e.theorems.exists(_.name == frflow.proof.lean.lower.LowerObligation.name(o.name).text)
    yield Judge.required(o.name, e)
    assertEquals(results.map(_.name).toSet, required.map(_.name).toSet, built._2)
    assertEquals(results.filter(_.status != ObligationStatus.Proven), Nil, built._2)
  }

  test("an example is shown from the claims; Lean's only errors are tries it did not prove".tag(LeanTag)) {
    val tries = obligations.collect { case o @ Obligation(_, _, Discharge.Attempt(_), _) => o }
    val shown = MiniProject.modules.flatMap(m => tries.map(o => Judge.tried(o.name, elaboration(m))))
      .filter(_.status == ObligationStatus.Shown).map(_.name)
    assertEquals(shown, List(frflow.proof.obligation.ObligationName.Example(0)), built._2)
    val failing = MiniProject.modules.flatMap { m =>
      val e = elaboration(m)
      e.diagnostics.filter(_.error).filterNot(d => e.theorems.exists(t => t.spans(d.line) &&
        tries.exists(o => frflow.proof.lean.lower.LowerObligation.name(o.name).text == t.name)))
    }
    assertEquals(failing, Nil, built._2)
  }
