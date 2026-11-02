package rooms

import frflow.*
import frflow.core.name.NodeId
import frflow.project.{Live, Ported, Projects}
import frflow.proof.lean.print.Print
import frflow.proof.obligation.ObligationName
import frflow.proof.verdict.{ObligationStatus, Result}
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

  test("isConstant of a Declaration changing with the World, with no program to change it: nothing to keep") {
    val fixed = spec("openingFixed")
    assert(fixed.contains("(∀ (world : World), True)"), fixed)
  }

  test("Lean proves the claim about the define reading state, its world bound below the room".tag(Live)) {
    Ported.run(Projects.elaborated(FrModel("Rooms")(ofTheirRoom)), Nil, Ported.Lean(Nil, Nil, None), Nil).map { r =>
      assertEquals(Ported.row(r.analysis, NodeId("ofTheirRoom")).take(3), List("claim", "proven", "proven"),
        Ported.table(r.analysis))
    }
  }

  private def standing(kb: FrModel, id: String) =
    Ported.run(Projects.elaborated(kb), Nil, Ported.Lean(Nil, Nil, None), Nil).map(r =>
      (Ported.row(r.analysis, NodeId(id)).take(3), Ported.table(r.analysis)))

  /** Whether Lean proves the theory consistent: some meaning of each Declaration meets every statement (2.8). */
  private def consistent(kb: FrModel) =
    Ported.run(Projects.elaborated(kb), Nil, Ported.Lean(Nil, Nil, None), Nil).map(r =>
      r.analysis.wholeCheck.toList.flatMap(_.results).collect {
        case Result(ObligationName.Consistent(_), s, _) => s
      })

  test("a claim that no run changes a Declaration is consistent with one giving its value (owner §44)".tag(Live)) {
    val fixed = Node.claim("The opening hour never changes.")(opening.isConstant)
    val nine = Node.claim("The rooms open at nine.")(opening === 9)
    consistent(FrModel("Rooms")(fixed, nine)).map(valued =>
      assert(valued.nonEmpty && valued.forall(_ == ObligationStatus.Proven), valued))
  }

  val store = Definition[BigInt => Flow[Unit]]("a number stored on the shelf")
  val storeCode = program { (n: Term[BigInt]) => Flow.step(frflow.eval.flow.Shelf.put(n)) }
  val oneShelf = Node.assumption("One at a time.")(frflow.eval.flow.Shelf.kept.atomic)
  val nothingElse = Node.assumption("Nothing but the programs change the shelf.")(
    frflow.eval.flow.Shelf.kept.onlyCodeChanges)
  private def failingRun(c: frflow.dsl.node.Node): FrModel =
    FrModel("Shelves")(c.assuming(oneShelf), nothingElse, oneShelf).implementProven(store)(storeCode)

  test("a run read as failing: Lean proves what a failed run leaves, and not a false one".tag(Live)) {
    import frflow.eval.flow.{Shelf, Trouble}
    val kept = Node.claim("A store that fails leaves the shelf as it was.")(
      forall((n: Term[BigInt]) => store(n).failing[Trouble].result.fold(
        _ => Shelf.kept.in(store(n).failing[Trouble].after) === Shelf.kept.current, _ => n === n)))
    val twice = Node.claim("A store that fails leaves the shelf holding the number twice more.")(
      forall((n: Term[BigInt]) => store(n).failing[Trouble].result.fold(
        _ => Shelf.kept.in(store(n).failing[Trouble].after) === Shelf.kept.current :+ n :+ n, _ => n === n)))
    for
      (k, kt) <- standing(failingRun(kept), "kept")
      (t, tt) <- standing(failingRun(twice), "twice")
    yield
      assertEquals(k.lift(2), Some("proven"), kt)
      assertNotEquals(t.lift(2), Some("proven"), tt)
  }

