package rooms

import frflow.*
import frflow.core.name.NodeId
import frflow.eval.flow.{Shelf, Trouble}
import frflow.project.{Live, Ported, Projects}
import frflow.proof.lean.print.Print
import frflow.proof.obligation.ObligationName
import scala.concurrent.duration.*

/** The semantics review's probes that Lean proved (scratchpad semantics-review.md), now not proven, and the new
  * meanings Lean is given (owner §44, §45): `isConstant` one equation per program, proven of a program that keeps the
  * value and not of one that changes it; a define's `forall` guarded as a statement's; a rule over a Declaration
  * that does not change with the World built and stated.
  */
class ReviewLeanSuite extends munit.CatsEffectSuite:
  override val munitIOTimeout: Duration = 40.minutes

  private def standing(kb: FrModel, id: String) =
    Ported.run(Projects.elaborated(kb), Nil, Ported.Lean(Nil, Nil, None), Nil).map(r =>
      (Ported.row(r.analysis, NodeId(id)).take(3), Ported.table(r.analysis)))

  private def module(kb: FrModel, name: String): String = Projects.bare(Projects.elaborated(kb)).modules
    .find(_.name.dotted == s"FrFlowGen.${kb.name.value}.$name").map(Print.module).getOrElse(fail(s"no $name"))

  val store = Definition[BigInt => Flow[Unit]]("a number stored on the shelf").failsWith[Trouble]
  val storeCode = program { (n: Term[BigInt]) => Flow.step(Shelf.put(n)) }
  val oneShelf = Node.assumption("One at a time.")(Shelf.kept.atomic)
  val nothingElse = Node.assumption("Nothing but the programs change the shelf.")(Shelf.kept.onlyCodeChanges)
  /** What a failed store leaves: the program's claim, beside the one about constancy. */
  val failedKeeps = Node.claim("A store that fails leaves the shelf as it was.")(
    forall((n: Term[BigInt]) => store(n).result.fold(
      _ => Shelf.kept.in(store(n).after) === Shelf.kept.current, _ => n === n))).assuming(oneShelf)
  private def shelf(c: frflow.dsl.node.Node): FrModel = FrModel("Shelves")(c.assuming(oneShelf, nothingElse),
    failedKeeps, nothingElse, oneShelf).implementProven(store)(storeCode)

  val stays = Node.claim("The shelf stays as it is.")(Shelf.kept.current.isConstant)
  val neverRemoved = Node.claim("A number on the shelf is never taken off it.")(
    forall((n: Term[BigInt]) => Shelf.kept.current.contains(n) implies Shelf.kept.current.contains(n).isConstant))

  test("isConstant is stated as one equation per program that changes what it reads, over its inputs") {
    val claim = module(shelf(stays), "stays.Spec")
    assert(claim.contains("store"), claim)
  }

  test("isConstant: Lean proves a number stored is never taken off, and not that the shelf never changes".tag(Live)) {
    for
      (kept, kt)    <- standing(shelf(neverRemoved), "neverRemoved")
      (changed, ct) <- standing(shelf(stays), "stays")
    yield
      assertEquals(kept.lift(2), Some("proven"), kt)
      assertNotEquals(changed.lift(2), Some("proven"), ct)
  }

  val ends = Node.assumption("Every booking ends after it starts.")(always[Booking](b => b.start < b.end))
  val someOverlap = define { (room: Term[String]) =>
    !forall((b: Term[Booking]) => (b.room === room) implies (b.start < b.end)) }
  val viaDefine = Node.claim("Some booking of every room ends before it starts.")(
    forall((room: Term[String]) => someOverlap(room)))

  test("a define's forall comes with what always holds of its variable, as a statement's does") {
    val d = module(FrModel("Rooms")(viaDefine, ends), "Domain.Def_someOverlap")
    assert(d.contains("Rooms.ends"), d)
  }

  test("finding 5: a claim through a define with a negated forall is not proven, as written inline it is not"
      .tag(Live)) {
    standing(FrModel("Rooms")(viaDefine, ends), "viaDefine").map((row, table) =>
      assertNotEquals(row.lift(2), Some("proven"), table))
  }

  val opening = Declaration[BigInt]("the hour the rooms open")
  val startsOpen = Node.assumption("Bookings start once the rooms are open.")(always[Booking](b => opening <= b.start))
  val nine = Node.claim("The rooms open at nine.")(opening === 9)

  test("finding 13: a rule over a Declaration that does not change with the World is built and stated".tag(Live)) {
    standing(FrModel("Rooms")(startsOpen, nine), "nine").map((row, table) =>
      assertEquals(row.lift(1), Some("proven"), table))
  }

  private val gAtomic = Node.assumption("One at a time.")(storedBookings.atomic)
  private val gOnly = Node.assumption("Only code.")(storedBookings.onlyCodeChanges)
  private val gStart = Node.assumption("Starts empty.")(storedBookings.initially(s => s === Nil))
  private val gGrant = Node.claim("Granted when no overlap.")(
    forall((held: Term[RoomBookings], request: Term[Booking]) =>
      granted(held, request) === held.bookings.forall(b => noOverlap(b, request)))).assuming(ends)
  private def rooms1(ns: frflow.dsl.node.Node*): FrModel =
    FrModel("Rooms")((ns.toList ++ List(gStart, gAtomic, gOnly, ends))*)
      .implementProven(book)(bookIfGranted)
      .implementTested(granted)(_ => (held, request) => Calendar(held).grants(request))
      .implementTested(inRoom, add)(start = BookingsTable.holding, observe = _.bookings)(t => (t.inRoom, t.add))
  private val ofRoomD = define { (room: Term[String]) => storedBookings.current.filter(b => b.room === room) }

  test("second review S1: conditions below book's run build in Lean, its code calling the tested calendar"
      .tag(Live)) {
    val j2 = Node.claim("A request answered booked is stored.")(
      forall((r: Term[Booking]) => book(r).result implies storedBookings.in(book(r).after).contains(r)))
      .assuming(gAtomic, ends)
    val j = Node.claim("A free request is answered booked.")(
      forall((r: Term[Booking]) => free(storedBookings.current, r) implies book(r).result))
      .assuming(gAtomic, ends)
    Ported.run(Projects.elaborated(rooms1(j2, j, gGrant.refines(j2, j))), Nil, Ported.Lean(Nil, Nil, None), Nil)
      .map { r =>
        val satisfiable = r.analysis.wholeCheck.toList.flatMap(_.results).filter(_.name match
          case ObligationName.Satisfiable(_, _) => true
          case _                                => false)
        assertEquals(satisfiable.map(_.name).toSet, Set(ObligationName.Satisfiable(NodeId("j2"), 0),
          ObligationName.Satisfiable(NodeId("j"), 0)))
        assert(satisfiable.forall(_.messages.forall(!_.error)), satisfiable)
      }
  }

  test("second review B1: the semantics review's W, its world named before the run, is proven".tag(Live)) {
    val wNeg = Node.claim("Once booked, the request was not among its room's bookings.")(
      forall((r: Term[Booking]) => book(r).result implies !ofRoomD(r.room).current.contains(r)))
      .assuming(gAtomic, ends)
    val claim = module(rooms1(wNeg, gGrant.refines(wNeg)), "wNeg.Spec")
    assert(claim.contains("(Rooms.ofRoomD r.room world)"), claim)
    standing(rooms1(wNeg, gGrant.refines(wNeg)), "wNeg").map((row, table) =>
      assertEquals(row.lift(2), Some("proven"), table))
  }
