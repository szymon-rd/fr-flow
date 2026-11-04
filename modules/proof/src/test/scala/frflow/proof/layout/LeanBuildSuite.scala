package frflow.proof.layout

import frflow.proof.lean.ast.LeanModule
import frflow.proof.lean.lower.LowerObligation
import frflow.proof.lean.print.Print
import frflow.proof.obligation.{Discharge, Obligation, ObligationName}
import frflow.proof.reading.{Elaboration, LeanOutput, ProofRules}
import frflow.proof.verdict.{Judge, ObligationStatus, Result}

/** A theory's modules built by Lean (`sbt leanTest`): every obligation FrFlow's automation or witnesses are to meet is
  * proven, as the judges read Lean's output, but those `open` names (each once per node it is asked of); every proof
  * audited rests on the axioms allowed only; the only errors are tries Lean did not prove (one-sided: they show
  * nothing) and the obligations left open.
  */
abstract class LeanBuildSuite(name: String, laid: => Laid, open: List[(String, ObligationName)])
    extends munit.FunSuite:
  override val munitTimeout: scala.concurrent.duration.Duration = scala.concurrent.duration.Duration(20, "minutes")

  protected lazy val built: String = LeanWorkspace.use(name)(_.build(laid.modules)._2)

  private def elaboration(m: LeanModule): Elaboration =
    Elaboration(Print.module(m), built, m.name.file.value.stripPrefix("lean/"))
  private def named(o: Obligation): String = LowerObligation.name(o.name).text

  /** Each obligation judged in the module of its owner whose theorem is named so. */
  protected def judged(os: List[(String, Obligation)], judge: (ObligationName, Elaboration) => Result)
      : List[(String, Result)] =
    for
      m      <- laid.modules
      e      = elaboration(m)
      (p, o) <- os if m.name.dotted.startsWith(p) && e.theorems.exists(_.name == named(o))
    yield p -> (if ran(m) then judge(o.name, e) else Result(o.name, ObligationStatus.Unchecked, Nil))

  /** Whether Lake ran Lean on the module: a module importing one that failed is not run. */
  private def ran(m: LeanModule): Boolean =
    built.linesIterator.exists(l => (l.startsWith("✔") || l.startsWith("ℹ") || l.startsWith("✖") ||
      l.startsWith("⚠")) && l.contains(s" ${m.name.dotted} "))

  private def required: List[(String, Obligation)] = laid.owned.filter((_, o) =>
    o.discharge == Discharge.Auto || o.discharge.isInstanceOf[Discharge.Witnessed])
  protected def tries: List[(String, Obligation)] = laid.owned.filter(_._2.discharge.isInstanceOf[Discharge.Attempt])
  private def unproven: Set[String] = (tries.map(_._2.name) ++ open.map(_._2)).map(LowerObligation.name(_).text).toSet

  test(s"$name: every required obligation is proven, but those left open".tag(LeanTag)) {
    val results = judged(required, Judge.required)
    assertEquals(results.size, required.size, built)
    val kb = s"FrFlowGen.${laid.kb}."
    assertEquals(results.filter(_._2.status != ObligationStatus.Proven).map((p, r) => s"$p ${r.name} ${r.status}")
      .sorted, open.map((n, o) => s"$kb$n. $o ${ObligationStatus.Open}").sorted, built)
  }

  test(s"$name: every proof audited rests on the axioms allowed only".tag(LeanTag)) {
    val axioms = LeanOutput.axioms(built)
    assert(axioms.nonEmpty, built)
    val audited = axioms.filter((t, _) => !unproven(t.split('.').last))
    assertEquals(audited.filter((_, as) => !as.forall(ProofRules.AllowedAxioms)), Map.empty, built)
  }

  test(s"$name: Lean's only errors are tries it did not prove".tag(LeanTag)) {
    val failing = laid.modules.flatMap { m =>
      val e = elaboration(m)
      e.diagnostics.filter(_.error)
        .filterNot(d => e.theorems.exists(t => t.spans(d.line) && unproven(t.name)))
    }
    assertEquals(failing, Nil, built)
  }
