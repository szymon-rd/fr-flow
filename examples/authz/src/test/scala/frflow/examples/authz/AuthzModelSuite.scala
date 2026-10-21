package frflow.examples.authz

import frflow.dsl.LayerKind
import frflow.examples.authz.domain.*
import frflow.lint.Lints
import frflow.model.TheoryModel
import frflow.render.LeanRenderer

/** The model without Lean: structure, generated Lean, and the running implementation. */
class AuthzModelSuite extends munit.FunSuite:

  private val m = TheoryModel.from(AuthzModel)

  test("the model is layered from requirements to an implementation, without lint errors") {
    assertEquals(m.topological.map(l => l.id -> l.kind),
      List("R0" -> LayerKind.Requirements, "D1" -> LayerKind.Design, "I2" -> LayerKind.Implementation))
    assertEquals(Lints.errors(Lints.run(m)), Nil)
  }

  test("the domain ADTs, their methods and companion values form the theory") {
    val t = m.theoryDefs.toSet
    Seq("UserId", "ResourceId", "Action", "Token", "Role", "Permission", "RbacPolicy", "Access",
      "RbacPolicy.permits", "RbacPolicy.revokeAll", "RbacPolicy.empty", "UserId.Anonymous").foreach { n =>
      assert(t(n), s"$n is not in the theory: $t")
    }
    assert(!t("SessionState"), "layer state types are not domain types")
  }

  test("every Lean definition is generated from Scala") {
    val r = LeanRenderer(m)
    val domain = r.renderDomain
    assert(domain.contains("inductive Action where\n  | Read\n  | Write\n  | Delete"), domain)
    assert(domain.contains("def RbacPolicy.permits (self : RbacPolicy) (user : UserId) (resource : ResourceId) (action : Action) : Prop"), domain)
    val i2 = r.renderModel(m.layerOrFail("I2"))
    assert(i2.contains("def Init (s : State) : Prop :=\n  s = (ServiceState.mk 0 (Scala.Map.empty"), i2)
    assert(i2.contains("def access.check (s : State) (p : Request) : Prop := ServiceState.allows s p"), i2)
  }

  test("the service runs the implementation") {
    val svc = AuthzService()
    val alice = UserId("alice")
    val bob = UserId("bob")
    val doc = ResourceId("/doc")
    val reader = Role("reader")
    assertEquals(svc.publish(RbacPolicy(Map(alice -> Set(reader)), Set(Permission(reader, doc, Action.Read)))), 1)
    assert(svc.login(alice, Token("a")))
    assert(!svc.login(bob, Token("a")), "a token in use cannot be reissued")
    assert(!svc.login(UserId.Anonymous, Token("x")), "Anonymous cannot log in")
    assert(svc.access(Token("a"), doc, Action.Read))
    assert(!svc.access(Token("a"), doc, Action.Write))
    assert(!svc.access(Token("nobody"), doc, Action.Read))
    svc.publish(RbacPolicy.empty)
    assert(!svc.access(Token("a"), doc, Action.Read), "the current policy decides")
    assertEquals(svc.state.log, List(Access(alice, doc, Action.Read, 1)))
  }

  test("the audit log of any run satisfies requirement Safe, evaluated in Scala") {
    // The theorem covers every run; this checks the Scala reading of the same property on one run.
    val svc = AuthzService()
    val users = List(UserId("u1"), UserId("u2"))
    val res = List(ResourceId("/a"), ResourceId("/b"))
    val role = Role("r")
    val rnd = scala.util.Random(7)
    (1 to 300).foreach { _ =>
      rnd.nextInt(4) match
        case 0 => svc.login(users(rnd.nextInt(2)), Token(s"t${rnd.nextInt(4)}"))
        case 1 => svc.logout(Token(s"t${rnd.nextInt(4)}"))
        case 2 => svc.publish(RbacPolicy(Map(users(rnd.nextInt(2)) -> Set(role)), Set(Permission(role, res(rnd.nextInt(2)), Action.Read))))
        case _ => svc.access(Token(s"t${rnd.nextInt(4)}"), res(rnd.nextInt(2)), Action.Read)
    }
    val sessionView = I2.abstractionCode.get.value(svc.state)
    val auditView = D1.abstractionCode.get.value(sessionView)
    assert(R0.invariants.head.code.value(auditView))
    assert(svc.state.log.nonEmpty)
  }
