package frflow.eval.run

import frflow.*
import frflow.core.analysis.Problem
import frflow.core.name.NodeId
import frflow.dsl.build.Fault
import frflow.eval.flow.{Shelf, Trouble}
import rooms.{Booking, BookingsTable, Calendar, add, book, bookIfGranted, booked, bookedIsStored, granted,
  inRoom, storedBookings}
import whole.Theories

/** The second 13b review's probes (scratchpad rebuild-review-step13b-2.md), as the reviewer wrote them: a world read
  * unnamed beside a run's result (B1); `.in` of a value read in no world unnamed, or of a run's outcome (B2); forms
  * that crashed now refused (S2); a program writing a model's state itself (S5).
  */
class SecondReviewSuite extends munit.FunSuite:
  private def faults(kb: FrModel): List[Fault] = Theories.errors(kb).map(_.fault)
  private val ends = Node.assumption("Every booking ends after it starts.")(always[Booking](b => b.start < b.end))
  private val gAtomic = Node.assumption("One at a time.")(storedBookings.atomic)
  private val gOnly = Node.assumption("Only code.")(storedBookings.onlyCodeChanges)
  private def withCode(ns: frflow.dsl.node.Node*): FrModel =
    FrModel("Rooms")((ns.toList ++ List(gAtomic, gOnly, ends))*)
      .implementProven(book)(bookIfGranted)
      .implementTested(granted)(_ => (held, request) => Calendar(held).grants(request))
      .implementTested(inRoom, add)(start = BookingsTable.holding, observe = _.bookings)(t => (t.inRoom, t.add))
  private val store = Definition[BigInt => Flow[Unit]]("a number stored on the shelf").failsWith[Trouble]
  private val shelfOnly = Node.assumption("Nothing but the programs change the shelf.")(Shelf.kept.onlyCodeChanges)

  private val ofRoomD = define { (room: Term[String]) => storedBookings.current.filter(b => b.room === room) }

  test("second review B1: a world read unnamed beside a run's result alone is refused (the semantics review's W)") {
    val wNeg = Node.claim("Once booked, the request is not among its room's bookings.")(
      forall((r: Term[Booking]) => book(r).result implies !ofRoomD(r.room).contains(r)))
    assertEquals(faults(withCode(wNeg)), List(Fault.WorldUnnamed(List("ofRoomD"))))
    val q = Node.claim("Once booked, the request is not booked.")(
      forall((r: Term[Booking]) => book(r).result implies !booked.contains(r)))
    assertEquals(faults(withCode(q, bookedIsStored)), List(Fault.WorldUnnamed(List("booked"))))
    val named = Node.claim("Once booked, the request was not among its room's bookings.")(
      forall((r: Term[Booking]) => book(r).result implies !ofRoomD(r.room).current.contains(r)))
    assertEquals(faults(withCode(named)), Nil)
  }

  test("second review B2: .in of a value read in no world unnamed, or of a run's outcome, is refused") {
    val c = Node.claim("Once booked, the request is not in the table after.")(
      forall((r: Term[Booking]) => book(r).result implies !storedBookings.current.in(book(r).after).contains(r)))
    val held = Node.claim("Once booked, the room's bookings after hold it.")(
      forall((r: Term[Booking]) =>
        val mine = ofRoomD(r.room).current
        book(r).result implies mine.in(book(r).after).contains(r)))
    val seq = Node.claim("Booking b after a succeeds.")(
      forall((a: Term[Booking], b: Term[Booking]) => book(b).result.in(book(a).after)))
    val inAfter = Node.claim("isConstant in after.")(
      forall((r: Term[Booking]) => storedBookings.current.isConstant.in(book(r).after)))
    List(c -> "of a value read in no world unnamed", held -> "of a value read in no world unnamed",
      seq -> "of a run's outcome", inAfter -> "of a value read in no world unnamed").foreach((n, what) =>
      assert(faults(withCode(n)).contains(Fault.InNamed(what)), (n.head.id, faults(withCode(n)))))
  }

  test("second review S2: refused forms are faults, never a FrFlow bug") {
    val nestedForall = Node.claim("nested forall.")(
      forall((r: Term[Booking]) => storedBookings.current.contains(r) implies
        forall((s: Term[Booking]) => storedBookings.current.contains(s).isConstant)))
    assertEquals(faults(withCode(nestedForall)), List(Fault.ConstantInside("under an inner forall")))
    @annotation.nowarn("msg=unused") val d = define { (n: Term[BigInt]) => always[Booking](b => b.start < b.end) }
    val notAlways = Node.claim("Not always.")(forall((n: Term[BigInt]) => !d(n)))
    assertEquals(faults(FrModel("Rooms")(notAlways)), List(Fault.AlwaysInside))
    val neverStores = program { (n: Term[BigInt]) => Flow.raise[Trouble, Unit](make[Trouble.TooBig](n)) }
    val putsFive = define { (n: Term[BigInt]) => Shelf.kept.in(store(5).after).contains(n) }
    val c1 = Node.claim("Five is put.")(putsFive(5))
    assertEquals(faults(FrModel("Shelves")(c1, shelfOnly).implementProven(store)(neverStores)),
      List(Fault.RunInside("store")))
    val c2 = Node.claim("Storing puts, via a define.")(forall((n: Term[BigInt]) =>
      val puts = define { (m: Term[BigInt]) => Shelf.kept.in(store(n).after).contains(m) }
      puts(n)))
    assertEquals(faults(FrModel("Shelves")(c2, shelfOnly).implementProven(store)(neverStores)),
      List(Fault.RunInside("store")))
    val unstarted = FrModel("Rooms")(ends, Node.claim("The table holds bookings.")(
      storedBookings.current === storedBookings.current))
    assert(Theories.problems(unstarted).contains(Problem.NoStart(NodeId("ends"), storedBookings.name)),
      Theories.problems(unstarted))
  }

  test("second review S5: a program writing a model's state without an operation is refused (the review's DW)") {
    import SecondReviewSuite.{emptyCode, emptying, jar}
    val jarOnly = Node.assumption("Nothing but the programs change the jar.")(jar.onlyCodeChanges)
    val jarOne = Node.assumption("One run at a time on the jar.")(jar.atomic)
    val says = Node.claim("Emptying empties.")(forall((n: Term[BigInt]) => jar.in(emptying(n).after) === Nil))
    val kept = Node.claim("A number in the jar is never taken out.")(
      forall((n: Term[BigInt]) => jar.current.contains(n) implies jar.current.contains(n).isConstant))
      .assuming(jarOnly, jarOne)
    val kb = FrModel("Jars")(kept, says, jarOnly, jarOne).implementProven(emptying)(emptyCode)
    assert(Theories.problems(kb).exists {
      case Problem.WritesState(_, m) => m == jar.name
      case _                         => false
    }, Theories.problems(kb))
  }

object SecondReviewSuite:
  /** A model whose state a program writes without an operation (the second review's `Direct.scala`). */
  val addD = Definition[BigInt => Flow[Unit]]("a number added to the jar")
  object jar extends StateModel[List[BigInt]]("the numbers in the jar"):
    addD.means(n => state.update(h => h :+ n))
    def raw: frflow.dsl.model.Model[List[BigInt]] = state

  val emptying = Definition[BigInt => Flow[Unit]]("the jar emptied directly")
  val emptyCode = program { (n: Term[BigInt]) => jar.raw.set(Nil).map(_ => n).map(_ => ()) }
