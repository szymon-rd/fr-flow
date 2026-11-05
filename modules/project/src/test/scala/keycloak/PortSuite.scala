package keycloak

import cats.effect.IO
import cats.syntax.all.*
import frflow.*
import frflow.core.name.NodeId
import frflow.proof.audit.Completeness
import frflow.project.{Captured, Live, Ported, Projects}
import frflow.project.Ported.Lean
import frflow.project.program.ModelCheck
import frflow.proof.obligation.ObligationName
import frflow.proof.verdict.{ObligationStatus, ProverRun, Result}
import frflow.testing.model.{ModelRuns, ModelTests}
import whole.Theories
import scala.concurrent.duration.*

/** Keycloak ported (owner §14, §21, §40), against today's (`reference/keycloak`, ARCHITECTURE section 9,
  * equivalence), its server's state the World's (owner §45 D): the store a model whose storing and index are known
  * only by what is assumed of them (G2), the server and the introspection programs over it, the requests the HTTP API
  * hands it a model of their own. Every difference in where a node sits and what it assumes is listed and judged;
  * checked by Lean and tested (the store's Scala on today's 1,000 runs from seed 1), each node stands as today's but
  * where judged; every consistency group proven (owner §28, §39); today's examples hold on the code; and each claim as
  * today stated it is proven equivalent to the port's (`resources/keycloak/port/Port.lean`).
  */
class PortSuite extends munit.CatsEffectSuite:
  override val munitIOTimeout: Duration = 50.minutes
  private val reference = Captured("keycloak")
  private val elaborated = Projects.elaborated(knowledge)
  private val t = elaborated.theory

  test("nothing is provided where the code runs: the history, the state and the accounts as loaded are the World's") {
    assertEquals(Ported.provided(elaborated), Set.empty[String])
    assertEquals(Ported.stoppedOnD(Judged.provided), Map.empty)
  }

  test("what is assumed of the draw reads only what it is shown, and the inbox's runs evaluate it: tested") {
    assertEquals(Theories.problems(knowledge), Nil)
    assertEquals(t.nodes.map(_.node.id).filter(id => frflow.core.checking.Assumed.untested(t, id).nonEmpty), Nil)
  }

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

  test("every difference from today's keycloak in where a node sits and what it assumes is listed and judged") {
    assertEquals(differences, Judged.differences.view.mapValues(_._1).toMap)
  }

  private val proofs = List("Lemmas", "realmAccess", "noUnauthorizedAccess", "signedInAreAccepted", "onlyTheSignedIn",
    "disabledHaveNoAccess", "rolesAsGranted", "sessionsMirrorSignIns", "accountsAsAdministered", "serverRun",
    "freshTokens", "oneSignInPerToken", "realmIsolation", "answersNameASession", "introspectAnswers", "loadedKept",
    "answersWhatItStores", "Whole")
  private val lean = Lean(proofs.map(n => n -> Ported.proof("keycloak", "Keycloak", n)),
    reference.old("Keycloak", identity) :+ ("FrFlowGen/Port.lean" -> Ported.resource("keycloak/port/Port.lean")),
    Some("FrFlowGen.Port"))
  private val written = List(RequestExamples())

  /** The store's Scala, run against what is assumed of its operations, today's 1,000 runs; and the inbox's, in its
    * tests' stand-in (an idle request when none waits), against what is assumed of what it hands on.
    */
  private def store: List[ModelCheck[IO]] =
    val idle = AuthRequest.SignOut(RealmId(""), "")
    def checked(m: frflow.core.vocab.StateModel, impl: frflow.core.code.Implementation) = ModelCheck(
      ModelRuns.reportedUnder(m.name), ModelRuns[IO](ModelTests.Check(m, impl), frflow.eval.Semantics(elaborated), t,
        1000).of(_, _))
    t.vocabulary.model(serverStore.name).toList.map(checked(_, ModelTests.of(serverStore)(start = SessionDb.holding,
      observe = (d: SessionDb) => d.stored)(d => (d.load, d.logged, d.record, d.lookup)))) ++
      t.vocabulary.model(inbox.name).toList.map(checked(_, ModelTests.of(inbox)(start = HttpInbox.holding,
        observe = (i: HttpInbox) => i.left)(i => Tuple1(i.nextOr(idle)(_)))))

  test("checked by Lean and tested, each node stands as today's but where judged; consistent; nothing weakened"
    .tag(Live)) {
    val examples = written.flatMap(_.elaborated.fold(e => fail(e.toString), identity))
    Ported.run(elaborated, examples, lean, store).map { r =>
      val a = r.analysis
      assertEquals(Completeness.of(a.decided, a.modules), Nil)
      val now = t.nodes.map(_.node.id).map(id => id.value.capitalize -> Ported.row(a, id)).toMap
      val compared = (reference.standings.keys ++ now.keys).toList.distinct.sorted
        .filter(k => now.get(k) != reference.standings.get(k)).map(k => k -> now.getOrElse(k, Nil))
      assertEquals(compared.toMap, Judged.standings, s"keycloak now:\n${Ported.table(a)}")
      assertEquals(Ported.unproven(a), Map.empty[String, List[String]])
      val whole = a.wholeCheck.map(_.results).getOrElse(fail("the theory's own check is not recorded"))
      assertEquals(whole.collect { case Result(n @ ObligationName.Consistent(_), s, _) => n -> s }.toMap,
        a.groups.map((i, _) => ObligationName.Consistent(i) -> ObligationStatus.Proven).toMap)
      r.port match
        case Some(ProverRun.Built(said)) => assert(!said.contains("sorryAx"), said)
        case other                       => fail(s"the claims are not shown equivalent to today's: $other")
    }
  }

  /** A store holding `s`, and the code run on it as production runs it. */
  private def on[A](s: Stored)(f: frflow.eval.Running[IO] => IO[A]): IO[A] =
    SessionDb.holding(s).flatMap(db => knowledge.running[IO](serverStore := db)).flatMap(f)

  test("today's examples hold on the code: the introspection's, the index's and the store's, each a run on a store") {
    val empty = Stored(loaded, ServerState(loaded, Nil), Nil)
    for
      intro  <- introspections.traverse(x => on(replayed)(_(introspecting)(x.inputs._1, x.inputs._2)).map(x -> _))
      looked <- lookups.traverse(x => SessionDb.holding(replayed).flatMap(_.lookup(x.inputs._1, x.inputs._2))
        .map(x -> _))
      stored <- stores.traverse(x => SessionDb.holding(empty).flatMap(_.record(x.inputs._1, x.inputs._2)).map(x -> _))
    yield
      (intro ++ looked ++ stored).foreach((x, got) => assertEquals(got == x.gives, x.holds, x.says))
      assertEquals((intro.size, looked.size, stored.size), (12, 5, 3))
  }

  test("today's request examples hold on the code") {
    assertEquals(frflow.testing.ported.Tested.onCode(RequestExamples()),
      List.fill(11)(frflow.eval.run.OnCode.Holds))
  }
