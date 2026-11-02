package sharing

import frflow.core.name.NodeId
import frflow.proof.audit.Completeness
import frflow.project.{Captured, Live, Ported, Projects, Tables as Models}
import frflow.project.Ported.Lean
import frflow.proof.obligation.ObligationName
import frflow.proof.verdict.{ObligationStatus, ProverRun, Result}
import scala.concurrent.duration.*

/** Sharing ported (owner §15, §28, §36, §41–§46), against today's (`reference/sharing`, ARCHITECTURE section 9,
  * equivalence): every difference in where a node sits and what it assumes is listed and judged (`Judged`); checked
  * by Lean and tested (the models' Scala on generated runs), each node stands as today's but where judged, what is
  * not proven is judged, and every consistency group is proven (owner §28); each claim as today stated it is proven
  * equivalent to the port's or listed (`resources/sharing/port/Port.lean`). Section 9's seeded bugs, the fault sweep
  * and the interleavings are `SeededSuite`'s.
  */
class PortSuite extends munit.CatsEffectSuite:
  override val munitIOTimeout: Duration = 90.minutes
  private val reference = Captured("sharing")
  private val elaborated = Projects.elaborated(knowledge)
  private val t = elaborated.theory

  private def differences: Map[String, String] =
    val now = t.nodes.map(_.node.id.value)
    val gone = reference.nodes.filterNot(now.contains).map(_ -> "gone")
    val added = now.filterNot(reference.nodes.contains).map(_ -> "new")
    val moved = now.filter(reference.nodes.contains).flatMap { n =>
      val id = NodeId(n)
      val parts = t.refinement.parts(id).map(_.value)
      val newParts = parts.filterNot(reference.parts(n).contains)
      val lost = reference.parts(n).filter(now.contains).filterNot(parts.contains)
      val assumes = t.refinement.assumed(id).map(_.value)
      val (more, less) = (assumes.filterNot(reference.assumes(n).contains),
        reference.assumes(n).filterNot(assumes.contains))
      List(Option.when(newParts.nonEmpty)(s"${newParts.mkString(", ")} ${if newParts.size == 1 then "is a part"
        else "are parts"}"),
        Option.when(lost.nonEmpty)(s"${lost.mkString(", ")} no part"),
        Option.when(more.nonEmpty || less.nonEmpty)("assumes " + (more.map("+" + _) ++ less.map("-" + _))
          .mkString(" "))).flatten.map(d => n -> d)
    }
    (gone ++ added ++ moved).groupMapReduce(_._1)(_._2)(_ + "; " + _)

  test("every value provided where the code runs is judged under owner §45 D") {
    assertEquals(Ported.provided(elaborated), Judged.provided.keySet)
  }

  test("every difference from today's sharing in where a node sits and what it assumes is listed and judged") {
    assertEquals(differences, Judged.differences.view.mapValues(_._1).toMap)
  }

  private val proofs = List("Lemmas", "canViewContract", "canEditContract", "housekeepingClearsOnlyTheEnded",
    "ownersKeepTheirDocuments", "trashUntilGone", "invitationsAreOffers", "accessRequestsAreAsks", "endedStaysEnded",
    "trashPurgedOnTime", "invitationsLapseOnTime", "requestsAnsweredOnTime", "auditTrail", "noticesFollowChanges",
    "accessFollowsShares", "handleContract", "housekeepingJob", "deliveryJob", "deliveryGivesBack", "Whole")
  private val lean = Lean(proofs.map(n => n -> Ported.resource(s"sharing/proofs/$n.lean")),
    reference.old("Sharing", Judged.oldOverNew) :+ ("FrFlowGen/Port.lean" -> Ported.resource("sharing/port/Port.lean")),
    Some("FrFlowGen.Port"))

  test(("checked by Lean and tested, each node stands as today's but where judged; what is not proven judged; " +
    "consistent; nothing weakened that is not listed").tag(Live)) {
    val examples = Examples.written.flatMap(_.elaborated.fold(e => fail(e.toString), identity))
    Ported.run(elaborated, examples, lean, Models.sqlite(elaborated)).map { r =>
      val a = r.analysis
      assertEquals(Completeness.of(a.decided, a.modules), Nil)
      val now = t.nodes.map(_.node.id).map(id => id.value.capitalize -> Ported.row(a, id)).toMap
      val compared = (reference.standings.keys ++ now.keys).toList.distinct.sorted
        .filter(k => now.get(k) != reference.standings.get(k)).map(k => k -> now.getOrElse(k, Nil))
      assertEquals(compared.toMap, Judged.standings, s"sharing now:\n${Ported.table(a)}")
      assertEquals(Ported.unproven(a), Judged.stopped)
      val whole = a.wholeCheck.map(_.results).getOrElse(fail("the theory's own check is not recorded"))
      assertEquals(whole.collect { case Result(n @ ObligationName.Consistent(_), s, _) => n -> s }.toMap,
        a.groups.map((i, _) => ObligationName.Consistent(i) -> ObligationStatus.Proven).toMap)
      r.port match
        case Some(ProverRun.Built(said)) => assert(!said.contains("sorryAx"), said)
        case other                       => fail(s"the claims are not shown equivalent to today's: $other")
    }
  }
