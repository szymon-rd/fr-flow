package whole

import auth.*
import frflow.*
import frflow.core.consistency.{Consistency, Group, Standing, Witness}
import frflow.core.name.{NodeId, SymbolName}
import frflow.core.vocab.ValueKind
import frflow.project.pipeline.Texts

/** Auth's purpose over Declarations (owner §14, §15): `authorized` and its peers are abstract, known only through
  * what refines them; each one's consistency witness is the equation that ties it to the domain.
  */
class AuthSuite extends munit.FunSuite:
  private val w = Whole(knowledge, Nil)
  private val t = w.resolved.theory
  private def names(ss: List[String]) = ss.map(SymbolName(_))

  test("authorized, signedIn and access are Declarations; grants and sessions Definitions provided where code runs") {
    assertEquals(List("authorized", "signedIn", "access", "grants", "sessions").map(s =>
      t.vocabulary.symbol(SymbolName(s)).map(_.kind)), List.fill(3)(Some(ValueKind.Declaration)) ++
      List.fill(2)(Some(ValueKind.Definition)))
  }

  test("each Declaration is its own group, witnessed by the equation of what refines it, for every table given") {
    assertEquals(Consistency.of(t).collect { case g: Group.Sharing => (g.statements, g.open, g.provided, g.witnesses) },
      List(
        (List(NodeId("grantsAuthorize")), names(List("authorized")), names(List("grants")),
          List(Witness.Equation(SymbolName("authorized"), NodeId("grantsAuthorize"),
            frflow.core.consistency.Picked.Right(0)))),
        (List(NodeId("sessionsSignIn")), names(List("signedIn")), names(List("sessions")),
          List(Witness.Equation(SymbolName("signedIn"), NodeId("sessionsSignIn"),
            frflow.core.consistency.Picked.Right(0)))),
        (List(NodeId("requestsReach")), names(List("access")), names(List("sessions", "grants")),
          List(Witness.Equation(SymbolName("access"), NodeId("requestsReach"),
            frflow.core.consistency.Picked.Right(0))))))
  }

  test("as Lean: for every grant table, some meaning of authorized makes grantsAuthorize true") {
    assertEquals(w.lean.head, "namespace Obl\n\n/-- grantsAuthorize hold together: some meaning of authorized makes " +
      "each true, for every grants provided. -/\n@[frflow_defs] def consistent_0 : Prop :=\n  ∀ (grants : " +
      "(List Grant)), ∃ (authorized : UserId → Path → Prop), (Auth.grantsAuthorize.claim authorized grants)\n\n" +
      "end Obl")
    assert(w.lean.contains("theorem consistent_0 : Obl.consistent_0 :=\n  fun grants => ⟨(fun (u : UserId) => " +
      "(fun (p : Path) => (∃ g ∈ grants, (g = (Grant.mk u p))))), by frflow_witness⟩"), w.lean)
  }

  test("with no equation for it, a Declaration leaves its group unwitnessed: consistency not proven, said so") {
    val alone = Whole(FrModel("Auth")(accessExactly), Nil).resolved.theory
    assertEquals(Consistency.of(alone).map(_.standing),
      List(Standing.Unwitnessed(names(List("access", "signedIn", "authorized")))))
    assertEquals(Texts.checking(alone, NodeId("accessExactly")).last,
      "consistent with accessExactly: consistency not proven")
  }

  test("R14.6: a group solved in substitution order: access is witnessed once signedIn and authorized are") {
    val signedInBySessions = Node.claim("A user is signed in exactly when a session is open for them.")(
      forall((u: Term[UserId]) => signedIn(u) === sessions.exists(s => s.user === u)))
    val authorizedByGrants = Node.claim("A user is authorized for a path exactly when a grant names them and it.")(
      forall((u: Term[UserId], p: Term[Path]) => authorized(u, p) === grants.exists(g => g === make[Grant](u, p))))
    val bottom = Whole(FrModel("Auth")(accessExactly, signedInBySessions, authorizedByGrants)
      .implementProvided(grants, sessions), Nil)
    val groups = Consistency.of(bottom.resolved.theory).collect { case g: Group.Sharing => (g.open, g.witnesses) }
    assertEquals(groups, List((names(List("access", "signedIn", "authorized")), List(
      Witness.Equation(SymbolName("signedIn"), NodeId("signedInBySessions"), frflow.core.consistency.Picked.Right(0)),
      Witness.Equation(SymbolName("authorized"), NodeId("authorizedByGrants"),
        frflow.core.consistency.Picked.Right(0)),
      Witness.Equation(SymbolName("access"), NodeId("accessExactly"), frflow.core.consistency.Picked.Right(0))))))
    assert(bottom.lean.exists(_.contains("⟨(fun (u : UserId) => (fun (p : Path) => (((fun (u : UserId) => " +
      "(∃ s ∈ sessions, (s.user = u))) u) ∧ ((fun (u : UserId) => (fun (p : Path) => (∃ g ∈ grants, " +
      "(g = (Grant.mk u p))))) u p)))), (fun (u : UserId) => (∃ s ∈ sessions, (s.user = u))), " +
      "(fun (u : UserId) => (fun (p : Path) => (∃ g ∈ grants, (g = (Grant.mk u p))))), by frflow_witness⟩")),
      bottom.lean)
  }
