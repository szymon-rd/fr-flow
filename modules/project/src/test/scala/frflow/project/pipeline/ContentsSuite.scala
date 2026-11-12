package frflow.project.pipeline

import frflow.core.Elaborated
import frflow.core.name.NodeId
import frflow.project.Projects

/** A node's decided form (`Contents.of`): each field once, in the one order; what its code is and, for a store
  * behaving as its model, the model as Lean is given it.
  */
class ContentsSuite extends munit.FunSuite:
  // Two examples analysed and lowered: beside the other suites, some seconds.
  override val munitTimeout: scala.concurrent.duration.Duration = scala.concurrent.duration.Duration(2, "minutes")
  private def lowered(e: Elaborated) = Projects.bare(e).canonical
  private val examples = List(Projects.rooms, Projects.elaborated(auth.knowledge))
  private val order = List("kind", "parents", "parts", "assumes", "statement", "formula", "written", "vocabulary",
    "checking", "writers", "governs", "call", "replaces", "reliance", "failure", "implementation", "model",
    "implementations")

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
    val c = Contents.of(lowered(Projects.rooms), NodeId("answerWhenNoOverlap"))
    assert(c.text("written").contains("bookings.book(request).result"), c.text("written"))
    assert(c.text("formula").startsWith("(∀ (x : Bookings), (∀ (x_1 : Booking),") &&
      c.text("formula").contains("Rooms.noOverlap"), c.text("formula"))
  }
