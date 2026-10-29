package frflow.project.program

import frflow.core.Elaborated
import frflow.project.Projects
import frflow.project.check.CheckPlan

/** The check's levels: each node Lean is asked of after what is below it, its parts and the callees its code relies
  * on among them, but its ancestors and, of a root proven of code, the other such roots (no circle orders them).
  */
class CheckPlanSuite extends munit.FunSuite:
  private val models: List[(String, () => Elaborated)] = List("crm" -> (() => Projects.elaborated(crm.knowledge)),
    "keycloak" -> (() => Projects.elaborated(keycloak.knowledge)), "rooms" -> (() => Projects.rooms))

  models.foreach { (name, e) =>
    test(s"$name: every node checked after what is below it, its parts among them: no circle") {
      val a = Projects.bare(e())
      val level = CheckPlan.levels(a, None).zipWithIndex.flatMap((ns, i) => ns.map(_ -> i)).toMap
      val late = level.keys.toList.flatMap(n => CheckPlan.below(a, n).filter(level.contains)
        .filterNot(b => level(b) < level(n)).map(n.value -> _.value))
      assertEquals(late, Nil)
      assert(level.keys.forall(n => a.decided.theory.refinement.parts(n).forall(p => !level.contains(p) ||
        CheckPlan.below(a, n).contains(p))))
    }
  }
