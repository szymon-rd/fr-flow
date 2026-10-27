package whole

import auth.*
import frflow.*
import frflow.core.consistency.{Consistency, Group, Picked, Standing, Witness}
import frflow.core.name.{NodeId, SymbolName}
import frflow.core.vocab.ValueKind

/** Auth's purpose over Declarations (owner §14, §15): `authorized` and its peers are abstract, known only through
  * what refines them; each one's consistency witness is the equation that ties it to the domain. (The groups' Lean is
  * `next-proof`'s.)
  */
class AuthSuite extends munit.FunSuite:
  private val t = Theories.resolved(knowledge).theory
  private def names(ss: String*) = ss.toList.map(SymbolName(_))
  private def groups(kb: FrModel) = Consistency.of(Theories.resolved(kb).theory).collect {
    case g: Group.Sharing => (g.statements.map(_.value), g.open, g.witnesses) }

  test("authorized, signedIn and access are Declarations; grants, sessions and admit Definitions") {
    assertEquals(List("authorized", "signedIn", "access", "grants", "sessions", "admit").map(s =>
      t.vocabulary.symbol(SymbolName(s)).map(_.kind)), List.fill(3)(Some(ValueKind.Declaration)) ++
      List.fill(3)(Some(ValueKind.Definition)))
  }

  test("each Declaration is in a group witnessed by the equation of what refines it, for every table given") {
    assertEquals(groups(knowledge).filter(_._2.exists(names("authorized", "signedIn").contains)), List(
      (List("grantTable"), names("authorized"),
        List(Witness.Equation(SymbolName("authorized"), NodeId("grantTable"), Picked.Right(0)))),
      (List("sessionTable"), names("signedIn"),
        List(Witness.Equation(SymbolName("signedIn"), NodeId("sessionTable"), Picked.Right(0))))))
  }

  test("access shares its group with the decision's claim on admit: each witnessed by its own equation") {
    val (statements, open, witnesses) = groups(knowledge).find(_._2.contains(SymbolName("access"))).get
    assertEquals((statements.toSet, open.toSet), (Set("requests", "decisionContract"), names("access", "admit").toSet))
    assertEquals(Standing.of(witnesses), Standing.Witnessed)
    assertEquals(witnesses.collect { case Witness.Equation(s, from, _) => s.value -> from.value }.toSet,
      Set("access" -> "requests", "admit" -> "decisionContract"))
  }

  test("with no equation for it, a Declaration leaves its group unwitnessed: consistency not proven, said so") {
    val alone = Theories.resolved(FrModel("Auth")(accessExactly)).theory
    assertEquals(Consistency.of(alone).map(_.standing),
      List(Standing.Unwitnessed(names("access", "signedIn", "authorized"))))
  }

  test("a group solved in substitution order: access is witnessed once signedIn and authorized are") {
    val signedInBySessions = Node.claim("A user is signed in exactly when a session is open for them.")(
      forall((u: Term[UserId]) => signedIn(u) === sessions.open.exists(s => s.user === u)))
    val authorizedByGrants = Node.claim("A user is authorized for a path exactly when a grant names them and it.")(
      forall((u: Term[UserId], p: Term[Path]) => authorized(u, p) === grants.exists(g => g === make[Grant](u, p))))
    val bottom = FrModel("Auth")(accessExactly, signedInBySessions, authorizedByGrants)
      .implementProvided(grants, sessions)
    assertEquals(groups(bottom), List((List("accessExactly", "signedInBySessions", "authorizedByGrants"),
      names("access", "signedIn", "authorized"), List(
        Witness.Equation(SymbolName("signedIn"), NodeId("signedInBySessions"), Picked.Right(0)),
        Witness.Equation(SymbolName("authorized"), NodeId("authorizedByGrants"), Picked.Right(0)),
        Witness.Equation(SymbolName("access"), NodeId("accessExactly"), Picked.Right(0))))))
  }
