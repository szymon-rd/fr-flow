package frflow.proof.layout

import frflow.proof.lean.ast.LeanModule
import frflow.proof.lean.lower.LowerObligation
import frflow.proof.lean.print.Print
import frflow.proof.obligation.{Discharge, Obligation, ObligationName}
import frflow.proof.reading.Elaboration
import frflow.proof.verdict.{Judge, ObligationStatus, Result}

/** A theory's modules built by Lean (`sbt leanTest`): every module but a node's checks builds; every obligation
  * FrFlow's automation or witnesses are to meet is proven, as the judges read Lean's output; the only errors are tries
  * Lean did not prove (one-sided: they show nothing).
  */
abstract class LeanBuildSuite(name: String, laid: => Laid) extends munit.FunSuite:
  override val munitTimeout: scala.concurrent.duration.Duration = scala.concurrent.duration.Duration(20, "minutes")

  protected lazy val built: String = LeanWorkspace.make(name).build(laid.modules)._2

  private def elaboration(m: LeanModule): Elaboration =
    Elaboration(Print.module(m), built, m.name.file.value.stripPrefix("lean/"))
  private def named(o: Obligation): String = LowerObligation.name(o.name).text

  /** Each obligation judged in the module whose theorem is named so. */
  protected def judged(os: List[Obligation], judge: (ObligationName, Elaboration) => Result): List[Result] =
    for
      m <- laid.modules
      e = elaboration(m)
      o <- os if e.theorems.exists(_.name == named(o))
    yield if ran(m) then judge(o.name, e) else Result(o.name, ObligationStatus.Unchecked, Nil)

  /** Whether Lake ran Lean on the module: a module importing one that failed is not run. */
  private def ran(m: LeanModule): Boolean =
    built.linesIterator.exists(l => (l.startsWith("✔") || l.startsWith("ℹ") || l.startsWith("✖") ||
      l.startsWith("⚠")) && l.contains(s" ${m.name.dotted} "))

  private def required: List[Obligation] = laid.obligations.filter(o =>
    o.discharge == Discharge.Auto || o.discharge.isInstanceOf[Discharge.Witnessed])
  protected def tries: List[Obligation] = laid.obligations.filter(_.discharge.isInstanceOf[Discharge.Attempt])

  test(s"$name: every required obligation is proven".tag(LeanTag)) {
    val results = judged(required, Judge.required)
    assertEquals(results.map(_.name).toSet, required.map(_.name).toSet, built)
    assertEquals(results.filter(_.status != ObligationStatus.Proven), Nil, built)
  }

  test(s"$name: Lean's only errors are tries it did not prove".tag(LeanTag)) {
    val failing = laid.modules.flatMap { m =>
      val e = elaboration(m)
      e.diagnostics.filter(_.error)
        .filterNot(d => e.theorems.exists(t => t.spans(d.line) && tries.exists(named(_) == t.name)))
    }
    assertEquals(failing, Nil, built)
  }
