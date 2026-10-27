package frflow.project.pipeline

import frflow.core.Elaborated
import frflow.core.analysis.{Resolve, Validate}
import frflow.core.name.NodeId
import frflow.decision.content.FieldValue
import frflow.project.Projects

/** A node's decided form (`Contents.of`): each field once, in the one order; what its code is and, for a store
  * behaving as its model, the model as Lean is given it.
  */
class ContentsSuite extends munit.FunSuite:
  private def resolved(e: Elaborated) = Resolve(Validate(e).fold(ps => fail(ps.toString), identity))
  private val examples = List(Projects.rooms, Projects.elaborated(auth.knowledge), Projects.elaborated(crm.knowledge),
    Projects.elaborated(sharing.knowledge))
  private val order = List("kind", "parents", "parts", "assumes", "statement", "formula", "vocabulary", "checking",
    "governs", "call", "replaces", "reliance", "failure", "implementation", "model", "implementations")

  test("every node of the examples has each field once, in the one order") {
    examples.map(resolved).foreach { r =>
      r.theory.nodes.map(_.node.id).foreach { id =>
        val names = Contents.of(r, id).fields.map(_._1)
        assertEquals(names.distinct, names, s"${r.theory.name.value}.${id.value}")
        assertEquals(names, order.filter(names.contains), s"${r.theory.name.value}.${id.value}")
      }
    }
  }

  test("a formula is the text the developer wrote") {
    assertEquals(Contents.of(resolved(Projects.rooms), NodeId("requestsEndAfterStart")).text("formula"),
      "always[Request](r => r.start < r.end)")
  }

  test("a claim on a Definition with plain Scala says the Scala; a proven program's claim, its program") {
    val r = resolved(Projects.rooms)
    def implementation(id: String) = Contents.of(r, NodeId(id)).text("implementation")
    assert(implementation("grantWhenNoOverlap").startsWith("granted: Scala, "), implementation("grantWhenNoOverlap"))
    assert(implementation("bookWhenFree").contains("book: proven program, "), implementation("bookWhenFree"))
  }

  test("the store behaving as its model: the model's operations as Lean is given them") {
    val model = Contents.of(resolved(Projects.rooms), NodeId("tableMatchesModel")).get("model")
    assert(model.exists {
      case FieldValue.Texts(lines) => lines.exists(_.contains("namespace StoredBookings")) &&
          lines.exists(_.contains("inRoom"))
      case _                       => false
    }, model)
  }
