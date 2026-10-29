package keycloak

import frflow.*
import frflow.core.name.NodeId
import frflow.eval.run.{Broken, OnCode}
import frflow.project.{Captured, Live, Ported, Projects}
import frflow.project.Ported.Lean
import frflow.proof.obligation.ObligationName
import frflow.proof.verdict.{ObligationStatus, ProverRun, Result}
import frflow.testing.ported.Tested
import scala.concurrent.duration.*

/** Keycloak ported (owner §14, §21, §40), against today's (`reference/keycloak`, ARCHITECTURE section 9,
  * equivalence): every difference in where a node sits and what it assumes is listed and judged; checked by Lean and
  * tested (1,000 cases from seed 1, as today), each node stands as today's but where judged; every consistency group
  * proven (owner §28, §39; the server's run with the state it holds solved by `serverRun`, the step 12 ruling on
  * provided values an assumption pins); section 9's seeded bugs are caught; today's examples
  * hold on the code; and no statement is weakened: each claim as today stated it is proven equivalent to the port's
  * (`resources/keycloak/port/Port.lean`).
  */
class PortSuite extends munit.CatsEffectSuite:
  override val munitIOTimeout: Duration = 50.minutes
  private val reference = Captured("keycloak")
  private val elaborated = Projects.elaborated(knowledge)
  private val t = elaborated.theory

  /** Each difference from today's keycloak, with why the design makes it. */
  private val judged: Map[String, (String, String)] = Map(
    "identities" -> ("gone" ->
      "it fixed four open types to realms and strings, which the Declarations' types now say (owner §15)"),
    "introspect" -> ("gone" -> "its claim is introspectAnswers, named apart from the Definition (owner §40)"),
    "introspectAnswers" -> ("new" -> "today's introspect, named apart from the Definition it is about (owner §40)"),
    "accountRoles" -> ("new" ->
      "today's accounts defined two words, enabled and rolesOf: a claim says what each Declaration is (2.7)"),
    "sessionsMirrorSignIns" -> ("serverRun is a part" -> serverRun),
    "accountsAsAdministered" -> ("serverRun is a part" -> serverRun),
    "onlyTheSignedIn" -> ("signInHistory, referenceTokens are parts" -> words),
    "disabledHaveNoAccess" -> ("accounts, referenceTokens, introspectAnswers are parts" -> words),
    "rolesAsGranted" -> ("accountRoles, referenceTokens, introspectAnswers are parts" -> words),
    "signedInAreAccepted" ->
      ("accounts, accountRoles, signInHistory, referenceTokens, introspectAnswers are parts" -> words),
    "answersNameASession" -> ("introspectAnswers is a part" -> renamed),
    "realmIsolation" -> ("introspectAnswers is a part" -> renamed))

  private def serverRun = "what the server's state is, trusted, is an assumption, a part of the claims resting on " +
    "it (owner §21); today's was a definition of sessions and account, which every node could use"
  private def words = "today's definitions of the purpose's words are claims saying what each Declaration is, below " +
    "the steps they are used in (2.7), with today's introspect, renamed (owner §40)"
  private def renamed = "today's introspect, which refined and kept it, renamed (owner §40)"

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
    assertEquals(differences, judged.view.mapValues(_._1).toMap)
  }

  /** Where each node stands apart from today, each for a reason the design gives. */
  private val standings: Map[String, List[String]] = Map(
    // Gone: the types say it; and today's introspect, renamed.
    "Identities" -> Nil,
    "Introspect" -> Nil,
    // Today's definitions, claims saying what each Declaration is (2.7): proven of what stands in them.
    "Accounts" -> List("claim", "proven", "proven", ""),
    "AccountRoles" -> List("claim", "proven", "proven", ""),
    "SignInHistory" -> List("claim", "proven", "proven", ""),
    "ReferenceTokens" -> List("claim", "proven", "proven", ""),
    // Today's definition of what the state is: trusted, an assumption (owner §21).
    "ServerRun" -> List("assumption", "assumed", "proven", ""),
    // A contract is a claim (owner §15); today's introspect named apart (owner §40), tested on today's cases.
    "HandleRequest" -> List("claim", "proven", "proven", ""),
    "IntrospectAnswers" -> List("claim", "tested", "proven", "1000"),
    // Claims mentioning introspect, tested against its Scala as well as proven from introspectAnswers (2.7).
    "AnswersNameASession" -> List("claim", "tested", "proven", "1000"),
    "RealmIsolation" -> List("claim", "tested", "proven", "1000"))

  private val proofs = List("Lemmas", "sessionsMirrorSignIns", "accountsAsAdministered", "oneSignInPerToken",
    "onlyTheSignedIn", "signedInAreAccepted", "Whole")
  private val lean = Lean(proofs.map(n => n -> Ported.resource(s"keycloak/proofs/$n.lean")),
    reference.old("Keycloak", identity) :+ ("FrFlowGen/Port.lean" -> Ported.resource("keycloak/port/Port.lean")),
    Some("FrFlowGen.Port"))
  private val written = List(IntrospectExamples(), LookupExamples(), StoreExamples(), RequestExamples())

  test("checked by Lean and tested, each node stands as today's but where judged; consistent; nothing weakened"
    .tag(Live)) {
    val examples = written.flatMap(_.elaborated.fold(e => fail(e.toString), identity))
    Ported.run(elaborated, examples, lean, Nil).map { r =>
      val a = r.analysis
      val now = t.nodes.map(_.node.id).map(id => id.value.capitalize -> Ported.row(a, id)).toMap
      val compared = (reference.standings.keys ++ now.keys).toList.distinct.sorted
        .filter(k => now.get(k) != reference.standings.get(k)).map(k => k -> now.getOrElse(k, Nil))
      assertEquals(compared.toMap, standings, s"keycloak now:\n${Ported.table(a)}")
      assertEquals(Ported.unproven(a), Map.empty[String, List[String]])
      val whole = a.wholeCheck.map(_.results).getOrElse(fail("the theory's own check is not recorded"))
      assertEquals(whole.collect { case Result(n @ ObligationName.Consistent(_), s, _) => n -> s }.toMap,
        a.groups.map((i, _) => ObligationName.Consistent(i) -> ObligationStatus.Proven).toMap)
      // What the world gives, freshTokens, holds of some history (the empty one), as every group taking it rests on.
      val fresh = a.groups.collectFirst { case (i, ids) if ids.contains(NodeId("freshTokens")) => i }
      assertEquals(fresh.flatMap(i => whole.find(_.name == ObligationName.Consistent(i))).map(_.status),
        Some(ObligationStatus.Proven))
      // Today's examples that give no value, the store's and the request's, are tried against the claims in Lean
      // too (owner §18), each shown: the request's by the step's code, given what storeKeepsState says of the
      // record that code leaves open.
      assertEquals(whole.collect { case Result(ObligationName.Example(i), s, _) => i -> s }.toMap,
        (17 to 30).map(_ -> ObligationStatus.Shown).toMap)
      r.port match
        case Some(ProverRun.Built(said)) => assert(!said.contains("sorryAx"), said)
        case other                       => fail(s"the claims are not shown equivalent to today's: $other")
    }
  }

  private type Looking = (RealmId, String) => Option[Session]
  private type Introspecting =
    (Looking, (RealmId, String) => Option[UserAccount]) => (RealmId, String) => Option[Claims]

  /** Keycloak with the store's index, its writes or the introspection given other code. */
  private def with_(looked: ServerState => Looking = s => SessionDb.holding(s).find,
      introspected: Introspecting = (lookUp, accountOf) => introspection(lookUp, accountOf),
      recorded: (AuthRequest, ServerState) => ServerState = (q, s) => SessionDb.holding(s).storeAfter(q, s)): FrModel =
    FrModel("Keycloak")(knowledge.nodes*).implementProvided(seed, history, state)
      .implementProven(step)(handle)
      .implementTested(record)(_ => recorded)
      .implementTested(lookup)(env => looked(env(state)))
      .implementTested(introspect, lookup, account)(env => introspected(env(lookup), env(account)))

  test("dropping store: a store that keeps the accounts and drops every session fails a case of storeKeepsState") {
    val dropping = with_(recorded = (_, after) => ServerState(after.accounts, Nil))
    assertEquals(Tested.failure(dropping, "storeKeepsState").broke, Broken.Post)
  }

  test("leaky introspection: an index answering with another realm's session fails a case of sessionLookup") {
    val leaky = with_(looked = _ => (_, token) => Some(Session(token, globex, "carol")))
    assertEquals(Tested.failure(leaky, "sessionLookup").broke, Broken.Post)
  }

  test("an introspection that forgets the account's state fails a generated case of introspectAnswers") {
    val forgetting = with_(introspected = (lookUp, accountOf) => (r, t) =>
      lookUp(r, t).flatMap(x => accountOf(r, x.user).map(a => Claims(r, x.user, a.roles))))
    assertEquals(Tested.failure(forgetting, "introspectAnswers").broke, Broken.Post)
  }

  test("today's examples hold on the code: the introspection's, the index's, the store's and the request's") {
    assertEquals(written.map(Tested.onCode), List(12, 5, 3, 11).map(List.fill(_)(OnCode.Holds)))
  }

  test("the code is tested with today's seed and cases: every claim on the introspection and the store, 1,000 " +
    "cases from seed 1") {
    assertEquals(Tested.nodes(knowledge).map(n => n -> Tested.passes(knowledge, n, written).seed.value).toMap,
      Map("introspectAnswers" -> 1L, "sessionLookup" -> 1L, "storeKeepsState" -> 1L, "realmIsolation" -> 1L,
        "answersNameASession" -> 1L))
  }
