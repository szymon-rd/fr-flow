package rooms

import frflow.*
import frflow.core.code.Code
import frflow.core.name.DefName
import frflow.dsl.build.Fault

/** The owner's core forms where they refuse (r43-owner-changes.md §15): exactly three kinds of nodes, two kinds of
  * values with the calling rule in the types, a claim on a Definition read as its call; and the forms of §6: a chain
  * of `implies` without its parentheses, a node's id its val's name as written.
  */
final case class Plain(n: BigInt)

class FormsSuite extends munit.FunSuite:
  private val bookable = Definition[(Boolean, Booking) => Boolean]("whether a booking can be made after another")
  val refused = Definition[(RoomBookings, Booking) => Boolean]("whether a request is refused")

  private val elsewhere = Node.claim("Granted only for a request no booking repeats.")(
    forall((held: Term[RoomBookings], request: Term[Booking]) =>
      granted(held, request) implies granted(make[RoomBookings](held.bookings.filter(b => b =!= request)), request)))
  private val inTurn = Node.claim("Bookings can be made in turn.")(
    (List.empty[Booking]: Term[List[Booking]]).foldLeft(True)((ok, b) => bookable(ok, b)))
  private val named = Node.claim("Granted exactly when not refused.")(
    forall((held: Term[RoomBookings], request: Term[Booking]) => granted(held, request) === !refused(held, request)))

  private val oneName = Node.claim("Every booking ends after it starts.")(forall((b: Term[Booking]) => b.start < b.end))
  private val anotherName = Node.claim("Every booking ends after it starts.")(
    forall((b: Term[Booking]) => b.start < b.end))

  test("three kinds of nodes and no other: a contract, an invariant, a definition node, an operation do not exist") {
    assert(compileErrors("""Node.contract(granted)("s")(True)""").nonEmpty)
    assert(compileErrors("""Node.invariant[Booking]("s")(b => b.start < b.end)""").nonEmpty)
    assert(compileErrors("""Node.definition("s")(True)""").nonEmpty)
    assert(compileErrors("""Operation[Booking => Boolean]("s")""").nonEmpty)
  }

  test("one Definition (R14.2): `define` and `program` make a Definition carrying its meaning; no Def type remains") {
    val d: Definition[(Booking, BigInt) => Boolean] = covers
    val p: Definition[Booking => Program[Boolean]] = bookIfGranted
    assertEquals((d.onTheSpot.map(_.code), p.onTheSpot.map(_.code)),
      (Some(Code.Proven(DefName("covers"))), Some(Code.ProvenFlow(DefName("bookIfGranted")))))
    assert(compileErrors("val one: Def1[Booking, Boolean] = ???").nonEmpty)
    assert(compileErrors("val more: Steps[Booking, Boolean] = ???").nonEmpty)
  }

  test("a meaning is given once: proven code is a define or a program, and one written on the spot takes no other") {
    def faults(kb: KnowledgeBase) = kb.elaborated.fold(_.iterator.map(_.fault).toList, _ => Nil)
    val notCode = Definition[Booking => Program[Boolean]]("a program nothing gives a meaning")
    assertEquals(faults(rooms.implementProven(book)(notCode)), List(Fault.NotProvenCode("notCode")))
    assertEquals(faults(rooms.implementTested(isFree)(_ => (_, _) => true)), List(Fault.MeantWhereWritten("isFree")))
    val runsItself = Node.claim("The program answers.")(
      forall((r: Term[Booking], w: Term[World]) => bookIfGranted(r).from(w) { (b, _) => b === b }))
    assertEquals(faults(KnowledgeBase("R")(runsItself)), List(Fault.ProgramMentioned("bookIfGranted")))
  }

  test("a Declaration is used only in statements: in a define or a program it does not compile, saying why") {
    val errors = compileErrors("""define { (u: Term[auth.UserId], p: Term[auth.Path]) => auth.authorized(u, p) }""")
    assert(errors.contains("a Declaration is used only in statements"), errors)
  }

  test("only a Definition takes a meaning: code for a Declaration does not compile") {
    assert(compileErrors("""auth.knowledge.implementTested(auth.authorized)(_ => (_, _) => true)""").nonEmpty)
  }

  test("a claim reads as a call of the Definition applied to its leading variables; another is an ordinary mention") {
    val call = RoomsLean.call(named.statement)
    assertEquals(call.definition.value, "granted")
    assertEquals(RoomsLean.define(call.posted), "(held : RoomBookings) (request : Booking) := " +
      "((granted held request) = (¬(refused held request)))")
  }

  test("a claim mentioning its Definition elsewhere too reads as no call: it is still a claim, checked as a whole") {
    assertEquals(List(elsewhere, inTurn).map(n => RoomsLean.elaborated(n.statement).call), List(None, None))
  }

  test("a chain of implies does not compile without its parentheses; with them, either grouping does") {
    val a: Term[Boolean] = True
    val (left, right) = ((a implies a) implies a, a implies (a implies a))
    assertEquals((left.expr == right.expr, compileErrors("a implies a implies a").contains("write the grouping")),
      (false, true))
  }

  test("a type that does not derive LeanType is named, with what to add") {
    val errors = compileErrors("define { (p: Term[Plain]) => True }")
    assert(errors.contains("Plain is not a domain type yet: add `derives LeanType` to its declaration"), errors)
  }

  test("a node's id is its val's name as written: renaming the val renames the node") {
    assertEquals((oneName.head.id.value, anotherName.head.id.value), ("oneName", "anotherName"))
  }
