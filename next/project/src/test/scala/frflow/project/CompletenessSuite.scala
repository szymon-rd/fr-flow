package frflow.project

import frflow.core.name.NodeId
import frflow.dsl.kb.FrModel
import frflow.proof.layout.{Completeness, Layout, NodePart}
import frflow.proof.lean.ast.Decl

/** Every rule of `always` the ported examples' Lean takes as a hypothesis is discharged, as an oracle reads it apart
  * from the obligations' own selection (`Completeness`): each store's start and each program changing it, each maker
  * of its type, each hand-off of one to code not proven. And the oracle sees an obligation gone.
  */
class CompletenessSuite extends munit.FunSuite:
  private val examples: List[(String, FrModel)] = List("rooms" -> _root_.rooms.rooms, "auth" -> _root_.auth.knowledge,
    "crm" -> _root_.crm.knowledge, "keycloak" -> _root_.keycloak.knowledge)

  examples.foreach { (name, kb) =>
    test(s"$name: every rule a statement assumes has its start, its cover_ and its made_ stated") {
      val a = Projects.bare(Projects.elaborated(kb))
      assertEquals(Completeness.of(a.decided, a.modules), Nil)
    }
  }

  test("an obligation gone from rooms' Lean is missed: a cover_, a made_ of a maker, the made_ at the calls") {
    val a = Projects.bare(Projects.rooms)
    val layout = Layout(a.decided.theory.name)
    def without(rule: String, obligation: String) = a.modules.map(m =>
      if m.name != layout.ofNode(NodeId(rule), NodePart.Spec) then m
      else m.copy(decls = m.decls.map {
        case Decl.Namespace(n, ds) => Decl.Namespace(n, ds.filterNot {
            case Decl.Documented(_, Decl.Def(_, x, _, _, _)) => x.text.startsWith(obligation)
            case _                                           => false
          })
        case other                 => other
      }))
    List("neverOverlap" -> "cover_book", "bookingsOfTheRoom" -> "made_inRoom",
      "bookingsOfTheRoom" -> "made_bookIfGranted_call_").foreach { (rule, obligation) =>
      assertEquals(Completeness.of(a.decided, without(rule, obligation)).map(m => (m.rule.value, m.obligation)),
        List(rule -> (if obligation.endsWith("_call_") then obligation + "<i>" else obligation)))
    }
  }
