package sharing

import cats.effect.IO
import frflow.core.name.NodeId
import frflow.eval.term.Semantics
import frflow.proof.audit.Completeness
import frflow.project.{Captured, Live, Ported, Projects}
import frflow.project.program.ModelCheck
import frflow.testing.model.{ModelRuns, ModelTests}
import sharing.store.{LibraryStore, SqliteLibraryStore}
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

  test("every value provided where the code runs stands under owner §45 D: the history and now are the World's") {
    assertEquals(Ported.provided(elaborated), Judged.provided.keySet)
    assertEquals(Ported.stoppedOnD(Judged.provided), Map.empty)
  }

  test("a cover_ puts in the code of what the program calls, as impl does (2.7): housekeeping tidying as its code") {
    val spec = Projects.bare(elaborated).modules
      .find(_.name.dotted == "FrFlowGen.Sharing.nothingEndedAtHousekeeping.Spec")
      .map(frflow.proof.lean.print.Print.module).getOrElse(fail("no nothingEndedAtHousekeeping spec"))
    val cover = spec.linesIterator.dropWhile(!_.contains("def cover_housekeep")).take(2).mkString("\n")
    assert(cover.contains("(Sharing.tidyCode (Sharing.goneCode 2592000)"), cover)
  }

  test("impl is stated for the fixed lifetimes the code and the claim read, not for every value of them (2.7)") {
    val spec = Projects.bare(elaborated).modules.find(_.name.dotted == "FrFlowGen.Sharing.isOpenContract.Spec")
      .map(frflow.proof.lean.print.Print.module).getOrElse(fail("no isOpenContract spec"))
    assert(spec.contains("(Sharing.isOpenContract.claim (Sharing.isOpenCode 604800) 604800)"), spec)
  }

  test("today's tests that need today's server or scheduler are listed, each deferred with why and to when") {
    assertEquals(Judged.deferred.size, 5)
    assert(Judged.deferred.values.forall(_.contains("with ")), Judged.deferred)
  }

  test("every node is stated against today's in Port.lean, or listed with why it is not") {
    val legacy = Map("canView" -> "canViewContract", "canEdit" -> "canEditContract", "inForce" -> "inForceContract",
      "isOpen" -> "isOpenContract", "gone" -> "goneContract", "pending" -> "pendingContract",
      "reminderDue" -> "reminderDueContract")
    val stated = """(?m)^theorem (\w+?)_(eq|today) """.r.findAllMatchIn(Ported.resource("sharing/port/Port.lean"))
      .map(_.group(1)).map(n => legacy.getOrElse(n, n)).toSet
    val nodes = t.nodes.map(_.node.id.value).toSet
    assertEquals(nodes -- stated, Judged.unstated.keySet)
    assertEquals(Judged.unstated.keySet -- nodes, Set.empty)
  }

  test("every difference from today's sharing in where a node sits and what it assumes is listed and judged") {
    assertEquals(differences, Judged.differences.view.mapValues(_._1).toMap)
  }

  private val proofs = List("Lemmas", "canViewContract", "canEditContract",
    "housekeepingClearsOnlyTheEnded", "ownersKeepTheirDocuments", "trashUntilGone", "invitationsAreOffers",
    "accessRequestsAreAsks", "auditTrail", "accessFollowsShares", "handleContract", "housekeepingJob", "deliveryJob",
    "deliveryGivesBack", "logKept", "nothingEndedAtHousekeeping", "timeMovesOn", "Whole")
  private val lean = Lean(proofs.map(n => n -> Ported.proof("sharing", "Sharing", n)),
    reference.old("Sharing", Judged.oldOverNew) :+ ("FrFlowGen/Port.lean" -> Ported.resource("sharing/port/Port.lean")),
    Some("FrFlowGen.Port"))

  /** Each model's Scala run against its model as today (`reference/sharing/seeds.txt`, from seed 1): the clock's and
    * the mail server's 1,000 times, the store's 1,200 (in memory 1,000, in SQLite 200), the pool's 1,000.
    */
  private def models: List[ModelCheck[IO]] =
    val semantics = Semantics(elaborated)
    ModelCheck.counted[IO](semantics, t, _ => 1000) ++
      t.vocabulary.model(LibraryStore.libraryModel.name).toList.map { model =>
        val check = ModelTests.Check(model, ModelTests.of(LibraryStore.libraryModel)(start = SqliteLibraryStore.holding,
          observe = (s: SqliteLibraryStore) => IO.blocking(s.library))(s => (s.load, s.save)))
        ModelCheck(ModelRuns.reportedUnder(model.name), ModelRuns[IO](check, semantics, t, 200).of(_, _))
      }

  test(("checked by Lean and tested, each node stands as today's but where judged; what is not proven judged; " +
    "consistent; nothing weakened that is not listed").tag(Live)) {
    val examples = Examples.written.flatMap(_.elaborated.fold(e => fail(e.toString), identity))
    Ported.run(elaborated, examples, lean, models).map { r =>
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
