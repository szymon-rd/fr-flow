package frflow.project.pipeline

import frflow.core.Elaborated
import frflow.core.name.NodeId
import frflow.decision.content.FieldValue
import frflow.project.Projects

/** A node's decided form (`Contents.of`): each field once, in the one order; what its code is and, for a store
  * behaving as its model, the model as Lean is given it.
  */
class ContentsSuite extends munit.FunSuite:
  private def lowered(e: Elaborated) = Projects.bare(e).canonical
  private val examples = List(Projects.rooms, Projects.elaborated(auth.knowledge), Projects.elaborated(crm.knowledge),
    Projects.elaborated(sharing.knowledge))
  private val order = List("kind", "parents", "parts", "assumes", "statement", "formula", "written", "vocabulary",
    "checking", "governs", "call", "replaces", "reliance", "failure", "implementation", "model", "implementations")

  test("every node of the examples has each field once, in the one order") {
    examples.map(lowered).foreach { r =>
      r.resolved.theory.nodes.map(_.node.id).foreach { id =>
        val names = Contents.of(r, id).fields.map(_._1)
        assertEquals(names.distinct, names, s"${r.kb.value}.${id.value}")
        assertEquals(names, order.filter(names.contains), s"${r.kb.value}.${id.value}")
      }
    }
  }

  test("a formula is what it means, as Lean is given it; what the developer wrote is shown beside it") {
    val c = Contents.of(lowered(Projects.rooms), NodeId("requestsEndAfterStart"))
    assertEquals(c.text("written"), "always[Request](r => r.start < r.end)")
    assert(c.text("formula").startsWith("(∀ (x : Request), (Rooms.requestsEndAfterStart x))") &&
      c.text("formula").contains("<"), c.text("formula"))
  }

  test("a claim on a Definition with plain Scala says the Scala; a proven program's claim, its program") {
    val r = lowered(Projects.rooms)
    def implementation(id: String) = Contents.of(r, NodeId(id)).text("implementation")
    assert(implementation("grantWhenNoOverlap").startsWith("granted: Scala, "), implementation("grantWhenNoOverlap"))
    assert(implementation("bookWhenFree").contains("book: proven program, "), implementation("bookWhenFree"))
  }

  test("the store behaving as its model: the model's operations as Lean is given them") {
    val model = Contents.of(lowered(Projects.rooms), NodeId("tableMatchesModel")).get("model")
    assert(model.exists {
      case FieldValue.Texts(lines) => lines.exists(_.contains("namespace StoredBookings")) &&
          lines.exists(_.contains("inRoom"))
      case _                       => false
    }, model)
  }
