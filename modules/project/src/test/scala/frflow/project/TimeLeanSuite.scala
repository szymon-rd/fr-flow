package frflow.project

import frflow.core.name.NodeId
import cats.syntax.all.*
import frflow.eval.flow.Stamps
import frflow.eval.time.{Extend, Frozen, Lapse, Late, Leans, MadeLeans, Outside4, Six, Sources5, Starts4}
import frflow.proof.obligation.{ObligationName, TryKind}
import frflow.proof.verdict.ObligationStatus
import scala.concurrent.duration.*

/** Time as Cats Effect models it (owner §47), checked by Lean: a rule time passing keeps is proven of the world's own
  * step (`cover_elapse`), a time limit fires only once its time passed, a race lost to a wait took the wait's
  * seconds, and two waits at once take the longer; the bugs time passing finds stay unproven: a rule it breaks, a
  * program relying on its own run taking no time, a time limit claimed never to fire, waits at once said to add up.
  */
class TimeLeanSuite extends munit.CatsEffectSuite:
  override val munitIOTimeout: Duration = 60.minutes

  test("what holds as time passes is proven: a rule time keeps, a limit firing late, a wait won, waits at once"
    .tag(Live)) {
    Ported.run(Projects.elaborated(Stamps.kept), Nil, Ported.Lean(Nil, Nil, None), Nil).map { r =>
      List("pastStamps", "stampsTheTime", "firesLate", "waitWins", "waitsAtOnce").foreach(n =>
        assertEquals(Ported.row(r.analysis, NodeId(n)).take(3).drop(1), List("proven", "proven"),
          s"$n\n${Ported.table(r.analysis)}"))
    }
  }

  test(("the bugs time passing finds stay unproven: a rule it breaks, a run taking no time, a limit never firing, " +
      "waits at once adding up, a wait taking less than its seconds under a schedule (the 13d review's B1), a time " +
      "said to stay where a run looking at it moves it (B2), a late look said to read the start (the re-review's " +
      "R-B2), a rule kept from one still open, by a cover_ (R-B1), a made_ (the third pass's R3-B1) or a start_ " +
      "(the fourth pass's P4-B1), a value rule stronger than what values from outside are assumed to meet (P4-B2), " +
      "broken by tested plain Scala or met by nothing (the fifth pass's P5-B1)")
      .tag(Live)) {
    List(Stamps.seeded -> List("freshStamps", "stampTakesNoTime", "neverGivenUp", "waitsAddUp", "waitWinsLate",
        "timeStill"), Lapse.lapse -> List("quick", "lately"), Extend.model -> List("stays"),
        Late.model -> List("readsStart"), Leans.model -> List("xZero", "yZero"),
        MadeLeans.model -> List("cellPositive", "posMade"), Starts4.model -> List("yZero", "yIsZero"),
        Outside4.model -> List("posRule", "storesPositive"), Sources5.tested -> List("posRule", "allPos"),
        Sources5.nested -> List("posRuleB", "firstStores"), Sources5.empty -> List("never", "allBelow"),
        Sources5.vacant -> List("never", "noneBelow"), Six.untried -> List("posRule", "aboveZero"))
      .traverse { (m, ns) =>
      Ported.run(Projects.elaborated(m), Nil, Ported.Lean(Nil, Nil, None), Nil).map { r =>
        val un = Ported.unproven(r.analysis)
        ns.foreach(n => assert(un.contains(n), s"$n\n${Ported.table(r.analysis)}"))
        // its root_impl is open beside readsStart's (a root reads root_impl open while a sibling root is)
        if m == Late.model then assertEquals(results(r, "readsLater").get(ObligationName.Impl),
          Some(ObligationStatus.Proven), Ported.table(r.analysis))
        // the failing test is mkGives', of the tested mkPos
        if m == Sources5.tested then
          assertEquals(r.analysis.tested(NodeId("mkGives")).flatMap(_.failure).map {
            case frflow.testing.report.Failure.Call(_, _, broke, _) => broke.toString
            case other                                               => other.toString
          }, Some("Always(posRule)"), Ported.table(r.analysis))
        // nothing breaks it here, no test runs: only its failing inhabited_ opens it
        if m == Sources5.vacant then assertEquals(r.analysis.broken, Set.empty, Ported.table(r.analysis))
        exact.getOrElse(m.name.value, Nil).map(n => s"${m.name.value}.$n" -> un.get(n))
      }
    }.map(found => assertEquals(found.flatten, expected))
  }

  /** Run with no model checks, as every run here: a statement resting on a model's tests is not tested, and a rule
    * not tested is open, so it names itself too.
    */
  private val exact: Map[String, List[String]] = Map("Leans" -> List("yZero"), "MadeLeans" -> List("posMade"),
    "Starts4" -> List("yIsZero"), "Outside4" -> List("posRule", "storesPositive"),
    "Sources5a" -> List("posRule", "allPos"), "Sources5c" -> List("never", "allBelow"),
    "Sources5d" -> List("never", "noneBelow"), "SevenA" -> List("posRule", "aboveZero"))
  private val expected: List[(String, Option[List[String]])] = List(
    "Leans.yZero" -> Some(List("Kept(yZero)", "Kept(xZero)", "NotTested")),
    "MadeLeans.posMade" -> Some(List("Kept(posMade)", "Kept(cellPositive)", "NotTested")),
    "Starts4.yIsZero" -> Some(List("Kept(yZero)", "NotTested")),
    "Outside4.posRule" -> Some(List("Check", "Kept(posRule)")),
    "Outside4.storesPositive" -> Some(List("Kept(posRule)", "NotTested")),
    "Sources5a.posRule" -> Some(List("Kept(posRule)")),
    "Sources5a.allPos" -> Some(List("Kept(posRule)")),
    "Sources5c.never" -> Some(List("Kept(never)")),
    "Sources5c.allBelow" -> Some(List("Kept(never)")),
    "Sources5d.never" -> Some(List("Kept(never)")),
    "Sources5d.noneBelow" -> Some(List("NothingBelow", "Kept(never)")),
    "SevenA.posRule" -> Some(List("Kept(posRule)")),
    "SevenA.aboveZero" -> Some(List("NothingBelow", "Kept(posRule)")))

  test(("a rule whose own standing is not proven, for any reason, is open: a tested maker's test failing on its " +
      "post first (the 13d sixth pass's P6-B1), a model's Scala failing its model test (P6-B2)").tag(Live)) {
    List(Six.postFirst, Six.wrongScala).traverse { m =>
      val e = Projects.elaborated(m)
      val models = frflow.project.program.ModelCheck.counted[cats.effect.IO](frflow.eval.term.Semantics(e), e.theory,
        _ => 200)
      Ported.run(e, Nil, Ported.Lean(Nil, Nil, None), models).map(r =>
        m.name.value -> Ported.unproven(r.analysis))
    }.map(found => assertEquals(found.toMap, Map[String, Map[String, List[String]]](
      // the maker's test fails on its post (mkWrong), naming no rule: posRule is open, and allPos resting on it
      "SixA" -> Map("posRule" -> List("Kept(posRule)"), "allPos" -> List("Kept(posRule)"),
        "mkStores" -> List("Consistency"), "mkWrong" -> List("Tests", "Consistency")),
      // the cell's Scala fails its model test: nonNeg is open, and sumAtLeast resting on it, on another model
      "SixB" -> Map("nonNeg" -> List("Kept(nonNeg)", "Tests"), "sumAtLeast" -> List("Kept(nonNeg)"),
        "puts" -> List("Kept(nonNeg)", "Tests"), "cellKept" -> List("Tests")))))
  }

  /** The module of `name` in the stamps' Lean, as printed. */
  private def printed(m: frflow.FrModel, name: String): String =
    Projects.bare(Projects.elaborated(m)).modules.find(_.name.dotted == name)
      .map(frflow.proof.lean.print.Print.module).getOrElse(fail(s"no $name"))

  test("time passing is asked of what reads the clock: a rule's cover_elapse, an isConstant's equation for elapse " +
      "and for a run whose only clock step is now (B2); waits at once end at the time reached where the sides " +
      "start; a late look given one first, whose tick is the time passing before it (R-B2)") {
    assert(printed(Stamps.seeded, "FrFlowGen.Stamping.freshStamps.Spec").contains("def cover_elapse"))
    assert(printed(Stamps.seeded, "FrFlowGen.Stamping.timeStill.Spec").contains("ClockModel.elapse_run"))
    assert(printed(Extend.model, "FrFlowGen.Extend.stays.Spec").contains("Extend.extendCode_run"))
    val late = printed(Late.model, "FrFlowGen.Late.Domain.Def_lateCode")
    assert(late.indexOf("ClockModel.Ops.now") > late.indexOf("ranAt") &&
      late.split("ClockModel.Ops.now", -1).length == 3, late)
    assert(printed(Stamps.kept, "FrFlowGen.Stamping.Domain.Def_waitedCode").contains("FrFlow.Waits.reach"))
  }

  /** The results of node `n`'s check, by obligation. */
  private def results(r: Ported.Run, n: String): Map[ObligationName, ObligationStatus] =
    r.analysis.current(NodeId(n)).toList.flatMap(_.results).map(x => x.name -> x.status).toMap

  test(("a schedule restricts the world's step between runs only (owner §47): a rule time passing alone breaks is " +
      "kept by elapse as scheduled, not by a run looking at the clock, after which the world moves the time freely")
      .tag(Live)) {
    Ported.run(Projects.elaborated(Stamps.scheduled), Nil, Ported.Lean(Nil, Nil, None), Nil).map { r =>
      val fresh = results(r, "freshWhileScheduled")
      assertEquals((fresh.get(ObligationName.Cover("elapse")), fresh.get(ObligationName.Cover("stamp")).exists(
        _ != ObligationStatus.Proven)), (Some(ObligationStatus.Proven), true), Ported.table(r.analysis))
      List("pastWhileScheduled", "stampsScheduled").foreach(n =>
        assertEquals(Ported.row(r.analysis, NodeId(n)).take(3).drop(1), List("proven", "proven"),
          s"$n\n${Ported.table(r.analysis)}"))
    }
  }

  test(("a schedule that lets no time pass from the start is warned of (its frozen try shown, the 13d review's S1); " +
      "one letting time pass is not").tag(Live)) {
    List(Frozen.model -> ("never", ObligationStatus.Shown), Lapse.lapse -> ("onTime", ObligationStatus.NotShown))
      .traverse_ { case (m, (n, status)) =>
        Ported.run(Projects.elaborated(m), Nil, Ported.Lean(Nil, Nil, None), Nil).map(r =>
          assertEquals(results(r, n).get(ObligationName.Tried(TryKind.Frozen)), Some(status), Ported.table(r.analysis)))
      }
  }
