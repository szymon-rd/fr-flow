package rooms

import frflow.*
import frflow.core.name.NodeId
import frflow.project.{Live, Ported, Projects}
import frflow.proof.lean.print.Print
import scala.concurrent.duration.*

/** What changes with the World, as Lean is given it (owner §43): a define reading state takes the world last and Lean
  * proves a claim about it; `isConstant` of a Declaration changing with the World is the same in every two worlds.
  */
class WorldLeanSuite extends munit.CatsEffectSuite:
  override val munitIOTimeout: Duration = 30.minutes

  val ofRoom = define { (room: Term[String]) => storedBookings.current.filter(b => b.room === room) }
  val ofTheirRoom = Node.claim("The table's bookings of a room are each of that room.")(
    forall((room: Term[String]) => ofRoom(room).forall(b => b.room === room)))
  val opening = Declaration[BigInt]("the hour the rooms open")
  val bookedAfterOpening = Node.claim("Every booking held starts once the rooms are open.")(
    storedBookings.current.forall(b => opening <= b.start))
  val openingFixed = Node.assumption("The opening hour never changes.")(opening.isConstant)
  private val kb = FrModel("Rooms")(ofTheirRoom, bookedAfterOpening, openingFixed)

  private def spec(id: String): String = Projects.bare(Projects.elaborated(kb)).modules
    .find(_.name.dotted == s"FrFlowGen.Rooms.$id.Spec").map(Print.module).getOrElse(fail(s"no $id"))

  test("a define reading state is a function of the world, its last input, called in the world the claim holds in") {
    val claim = spec("ofTheirRoom")
    assert(claim.contains("(∀ (room : String), (∀ (world : World), "), claim)
    assert(claim.contains("(Rooms.ofRoom room world)"), claim)
  }

  test("isConstant of a Declaration changing with the World: the same in every two worlds") {
    val fixed = spec("openingFixed")
    assert(fixed.contains("(∀ (w1 : World), (∀ (w2 : World), ((opening w1) = (opening w2))))"), fixed)
  }

  test("Lean proves the claim about the define reading state, its world bound below the room".tag(Live)) {
    Ported.run(Projects.elaborated(FrModel("Rooms")(ofTheirRoom)), Nil, Ported.Lean(Nil, Nil, None), Nil).map { r =>
      assert(!Ported.unproven(r.analysis).contains(NodeId("ofTheirRoom").value), Ported.table(r.analysis))
    }
  }
