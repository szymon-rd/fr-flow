package rooms

import frflow.*
import frflow.core.analysis.Problem
import frflow.core.code.{Code, Values}
import frflow.core.expr.Exprs
import frflow.core.name.{DefName, NodeId, SymbolName}
import frflow.dsl.build.Fault
import frflow.dsl.flow.Recorded
import whole.Theories

/** The owner's core forms where they refuse (owner-decisions.md §15, §19, §21): exactly three kinds of nodes, two
  * kinds of values with the calling rule in the types, two quantifiers, statements about values only, a claim on a
  * Definition read as its call; and the forms of §6: a chain of `implies` without its parentheses, a node's id its
  * val's name as written.
  */
final case class Plain(n: BigInt)

/** What a connection to a database is to the code: no domain type. */
final case class Connection(url: String)

/** A record whose `derives LeanType` was forgotten. */
final case class Wire(host: String)

class FormsSuite extends munit.FunSuite:
  private val bookable = Definition[(Boolean, Booking) => Boolean]("whether a booking can be made after another")
  val refused = Definition[(RoomBookings, Booking) => Boolean]("whether a request is refused")

  private val elsewhere = Node.claim("Granted only for a request no booking repeats.")(
    forall((held: Term[RoomBookings], request: Term[Booking]) => granted(held, request) implies
      granted(make[RoomBookings](held.room, held.bookings.filter(b => b =!= request)), request)))
  private val inTurn = Node.claim("Bookings can be made in turn.")(
    (Nil: Term[List[Booking]]).foldLeft(True)((ok, b) => bookable(ok, b)))
  private val named = Node.claim("Granted exactly when not refused.")(
    forall((held: Term[RoomBookings], request: Term[Booking]) => granted(held, request) === !refused(held, request)))

  /** That the code does not compile, for the reason given. */
  private def fails(errors: String, why: String): Unit = assert(errors.contains(why), errors)

  private val oneName = Node.claim("Every booking ends after it starts.")(forall((b: Term[Booking]) => b.start < b.end))
  private val anotherName = Node.claim("Every booking ends after it starts.")(
    forall((b: Term[Booking]) => b.start < b.end))

  test("three kinds of nodes and no other: a contract, an invariant, a definition node, an operation do not exist") {
    fails(compileErrors("""Node.contract(granted)("s")(True)"""), "value contract is not a member of object")
    fails(compileErrors("""Node.invariant[Booking]("s")(b => b.start < b.end)"""),
      "value invariant is not a member of object")
    fails(compileErrors("""Node.definition("s")(True)"""), "value definition is not a member of object")
    fails(compileErrors("""Operation[Booking => Boolean]("s")"""), "Not found: Operation")
  }

  test("two quantifiers and no other: forall and always; `exists` is a list's, never a statement's") {
    assert(compileErrors("forall((t: Term[BigInt]) => t === t)").isEmpty)
    assert(compileErrors("always[Booking](b => b.start < b.end)").isEmpty)
    fails(compileErrors("exists((t: Term[BigInt]) => t === t)"),
      "None of the overloaded alternatives of method exists")
  }

  test("statements are about values only (owner §21): no assumption on what a Definition is called with") {
    fails(compileErrors("outside.calls(book)"), "Not found: outside")
    fails(compileErrors("book.calledOnlyWith(r => r.start < r.end)"), "value calledOnlyWith is not a member of")
    assert(compileErrors("Node.assumption(\"s\")(always[Request](r => r.start < r.end))").isEmpty)
  }

  test("one Definition: `define` and `program` make a Definition carrying its meaning; no Def type remains") {
    val d: Definition[(Booking, BigInt) => Boolean] = covers
    val p: Definition[Request => Program[Boolean]] = bookIfGranted
    assertEquals((d.onTheSpot.map(_.code), p.onTheSpot.map(_.code)),
      (Some(Code.Proven(DefName("covers"))), Some(Code.ProvenFlow(DefName("bookIfGranted")))))
    fails(compileErrors("val one: Def1[Booking, Boolean] = ???"), "Not found: type Def1")
    fails(compileErrors("val more: Steps[Booking, Boolean] = ???"), "Not found: type Steps")
  }

  test("a program takes up to six inputs, each a variable of its recorded steps, named as written") {
    val six = program { (a: Term[BigInt], b: Term[BigInt], c: Term[BigInt], d: Term[BigInt], e: Term[BigInt],
        g: Term[BigInt]) => Flow[Recorded].pure(a + b + c + d + e + g) }
    assertEquals(RoomsIr.lambda(six).value.params.map(_.hint), List("a", "b", "c", "d", "e", "g"))
  }

  test("a meaning is given once: proven code is a define or a program, and one written on the spot takes no other") {
    def faults(kb: KnowledgeBase) = kb.elaborated.fold(_.iterator.map(_.fault).toList, _ => Nil)
    val notCode = Definition[Request => Program[Boolean]]("a program nothing gives a meaning")
    assertEquals(faults(rooms.implementProven(book)(notCode)), List(Fault.NotProvenCode("notCode")))
    assertEquals(faults(rooms.implementTested(free)(_ => (_, _) => true)), List(Fault.MeantWhereWritten("free")))
    val runsItself = Node.claim("The program answers.")(
      forall((r: Term[Request], w: Term[World]) => bookIfGranted(r).from(w) { (b, _) => b === b }))
    assertEquals(faults(KnowledgeBase("R")(runsItself)), List(Fault.ProgramMentioned("bookIfGranted")))
  }

  test("a Declaration is used only in statements: in a define or a program it does not compile, saying why") {
    val errors = compileErrors("""define { (u: Term[auth.UserId], p: Term[auth.Path]) => auth.authorized(u, p) }""")
    assert(errors.contains("a Declaration is used only in statements"), errors)
  }

  test("only a Definition takes a meaning: code for a Declaration does not compile") {
    fails(compileErrors("""auth.knowledge.implementTested(auth.authorized)(_ => (_, _) => true)"""),
      "Required: frflow.dsl.vocab.Definition[F]")
  }

  test("a claim reads as a call of the Definition applied to its leading variables; another is an ordinary mention") {
    val call = RoomsIr.call(named.statement)
    assertEquals(call.definition, SymbolName("granted"))
    assertEquals(call.posted.value.params.map(_.hint), List("held", "request"))
    assertEquals(Exprs.mentions(call.posted.value.body).symbols.toSet,
      Set(SymbolName("granted"), SymbolName("refused")))
  }

  test("a claim mentioning its Definition elsewhere too reads as no call: it is still a claim, checked as a whole") {
    assertEquals(List(elsewhere, inTurn).map(n => RoomsIr.elaborated(n.statement).call), List(None, None))
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

  test("a Definition of a type with no LeanType is code-only: provided to code, read there; never in a statement") {
    val connection = Definition[Connection]("the connection the code is given where it runs")
    val connected = Node.claim("The connection is the one given.")(connection === connection)
    assert(connection.codeOnly && !granted.codeOnly)
    assertEquals(Theories.problems(rooms.implementProvided(connection)), Nil)
    assertEquals(Theories.problems(KnowledgeBase("Wired")(connected).implementProvided(connection)),
      List(Problem.CodeOnlyInStatement(NodeId("connected"), SymbolName("connection"), "Connection")))
    val db = Connection("jdbc:sqlite:rooms.db")
    assertEquals(Values(Map(SymbolName("connection") -> (() => db))).apply(connection), db)
  }

  test("a record whose derives LeanType is forgotten: its field selected in a statement names the type, code-only") {
    val wire = Definition[Wire]("the wire the code is given where it runs")
    val wired = Node.claim("The wire goes to the database.")(wire.host === "db")
    assertEquals(Theories.errors(KnowledgeBase("Wired")(wired).implementProvided(wire)).map(_.fault),
      List(Fault.CodeOnlyInStatement("Wire")))
  }

  test("a node's id is its val's name as written: renaming the val renames the node") {
    assertEquals((oneName.head.id.value, anotherName.head.id.value), ("oneName", "anotherName"))
  }
