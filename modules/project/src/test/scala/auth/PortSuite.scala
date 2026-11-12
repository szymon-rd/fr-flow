package auth

import frflow.*
import frflow.core.expr.Value
import frflow.core.name.NodeId
import frflow.eval.run.{Broken, OnCode}
import frflow.proof.audit.Completeness
import frflow.project.{Captured, Live, Ported, Projects}
import frflow.project.Ported.Lean
import frflow.proof.obligation.ObligationName
import frflow.proof.verdict.{ObligationStatus, ProverRun, Result}
import frflow.testing.ported.Tested
import frflow.testing.report.Failure
import scala.concurrent.duration.*

/** Auth ported (owner §14, §21, §40), against today's (`reference/auth`, ARCHITECTURE section 9, equivalence): every
  * difference in where a node sits and what it assumes is listed and judged; checked by Lean and tested (1,000 cases
  * from seed 1, as today), each node stands as today's but where judged, and every consistency group is proven (owner
  * §28); the seeded bug is caught; the examples hold on the code; and no statement is weakened: each claim as today
  * stated it is proven equivalent to the port's (`resources/auth/port/Port.lean`).
  */
class PortSuite extends munit.CatsEffectSuite:
  override val munitIOTimeout: Duration = 40.minutes
  private val reference = Captured("auth")
  private val elaborated = Projects.elaborated(knowledge)
  private val t = elaborated.theory

  test("every value provided where the code runs stands under owner §45 D: the tables stay provided (owner §48)") {
    assertEquals(Ported.provided(elaborated), Judged.provided.keySet)
    assertEquals(Ported.stoppedOnD(Judged.provided), Map.empty)
  }

  private def differences: Map[String, String] =
    val now = t.nodes.map(_.node.id.value)
    val gone = reference.nodes.filterNot(now.contains).map(_ -> "gone")
    val added = now.filterNot(reference.nodes.contains).map(_ -> "new")
    val moved = now.filter(reference.nodes.contains).flatMap { n =>
      val id = NodeId(n)
      val parts = t.refinement.parts(id).map(_.value)
      val newParts = parts.filterNot(reference.parts(n).contains)
      val assumes = t.refinement.assumed(id).map(_.value)
      val (more, less) = (assumes.filterNot(reference.assumes(n).contains),
        reference.assumes(n).filterNot(assumes.contains))
      List(Option.when(newParts.nonEmpty)(s"${newParts.mkString(", ")} ${if newParts.size == 1 then "is a part"
        else "are parts"}"),
        Option.when(more.nonEmpty || less.nonEmpty)("assumes " + (more.map("+" + _) ++ less.map("-" + _))
          .mkString(" "))).flatten.map(n -> _)
    }
    (gone ++ added ++ moved).toMap

  test("every difference from today's auth in where a node sits and what it assumes is listed and judged") {
    assertEquals(differences, Judged.differences.view.mapValues(_._1).toMap)
  }

  private val proofs = List("Lemmas", "accessExactly", "tokenNamesHolder", "accessNeedsGrant", "grantLetsIn")
  private val lean = Lean(proofs.map(n => n -> Ported.proof("auth", "Auth", n)),
    reference.old("Auth", identity) :+ ("FrFlowGen/Port.lean" -> Ported.resource("auth/port/Port.lean")),
    Some("FrFlowGen.Port"))

  test("checked by Lean and tested, each node stands as today's but where judged; consistent; nothing weakened"
    .tag(Live)) {
    Ported.run(elaborated, DecisionExamples().elaborated.fold(e => fail(e.toString), identity), lean, Nil).map { r =>
      val a = r.analysis
      assertEquals(Completeness.of(a.decided, a.modules), Nil)
      val now = t.nodes.map(_.node.id).map(id => id.value.capitalize -> Ported.row(a, id)).toMap
      val compared = (reference.standings.keys ++ now.keys).toList.distinct.sorted
        .filter(k => now.get(k) != reference.standings.get(k)).map(k => k -> now.getOrElse(k, Nil))
      assertEquals(compared.toMap, Judged.standings, s"auth now:\n${Ported.table(a)}")
      assertEquals(Ported.unproven(a), Map.empty[String, List[String]])
      val whole = a.wholeCheck.map(_.results).getOrElse(fail("the theory's own check is not recorded"))
      assertEquals(whole.collect { case Result(n @ ObligationName.Consistent(_), s, _) => n -> s }.toMap,
        a.groups.map((i, _) => ObligationName.Consistent(i) -> ObligationStatus.Proven).toMap)
      r.port match
        case Some(ProverRun.Built(said)) => assert(!said.contains("sorryAx"), said)
        case other                       => fail(s"the claims are not shown equivalent to today's: $other")
    }
  }

  test("the seeded bug: a decision that ignores the grant table fails a generated case of decisionContract") {
    val careless = FrModel("Auth")(knowledge.nodes*).defining(grants.provided, sessions.provided)
      .defining(admit.defineTested(env => (t, _) => env(sessions).open.find(_.token == t).map(_.user)))
    Tested.failure(careless, "decisionContract") match
      case Failure.Call(List(Value.Str(_), _), _, Broken.Post, _) => ()
      case other                                                 => fail(s"not caught: $other")
  }

  test("today's examples hold on the code, each checked in Scala only (it sets the tables)") {
    assertEquals(Tested.onCode(DecisionExamples()), List.fill(5)(OnCode.Holds))
  }

  test("the code is tested with today's seed and cases: every claim on admit, 1,000 cases from seed 1") {
    assertEquals(Tested.nodes(knowledge).map(n => n -> Tested.passes(knowledge, n, List(DecisionExamples())).seed
      .value).toMap, Map("tokenNamesHolder" -> 1L, "accessNeedsGrant" -> 1L, "grantLetsIn" -> 1L,
      "decisionContract" -> 1L))
  }

  test("the server decides a request by admit's code, given the tables: Alice's token and grant let her in") {
    val decide = service(List(Grant(UserId("alice"), Path("/a"))), Sessions(List(Session("t1", UserId("alice")))))
    assertEquals((decide("t1", Path("/a")), decide("t1", Path("/b"))), (Some(UserId("alice")), None))
  }
