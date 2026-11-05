package rooms

import frflow.*
import frflow.core.analysis.{Constancy, Problem}
import frflow.core.analysis.outside.Premise
import frflow.core.consistency.{Consistency, Vacuity}
import frflow.core.expr.{Expr, Exprs}
import frflow.core.name.{ModelName, NodeId, SymbolName}
import frflow.dsl.build.Fault
import frflow.eval.Semantics
import frflow.eval.flow.{Shelf, Trouble}
import frflow.eval.run.{ExampleRun, OnCode}
import whole.Theories

/** The semantics review's probes (scratchpad semantics-review.md, owner §44, §45), each now refused where its
  * reading would not be the one written, or read as written: an `always` inside a formula, a world read unnamed
  * beside a run's world after, the worlds after two runs, `isConstant` where no step keeps it and its meaning (one
  * equation per program that changes what it reads), a rule over a Declaration that changes with the World, a plain
  * reading of a program that can fail, an example's value breaking a rule, and the vacuity checks under a run.
  */
class ReviewSuite extends munit.FunSuite:
  private def faults(kb: FrModel): List[Fault] = Theories.errors(kb).map(_.fault)
  private def formula(kb: FrModel, id: String): Expr =
    Theories.theory(kb).nodes.map(_.node).find(_.id.value == id).flatMap(_.statement.said).map(_.value)
      .getOrElse(fail(s"no $id"))

  private val ends = Node.assumption("Every booking ends after it starts.")(always[Booking](b => b.start < b.end))
  private val gAtomic = Node.assumption("One at a time.")(storedBookings.atomic)
  private val gOnly = Node.assumption("Only code.")(storedBookings.onlyCodeChanges)
  private def withCode(ns: frflow.dsl.node.Node*): FrModel =
    FrModel("Rooms")((ns.toList ++ List(gAtomic, gOnly, ends))*)
      .implementProven(book)(bookIfGranted)
      .implementTested(granted)(_ => (held, request) => Calendar(held).grants(request))
      .implementTested(inRoom, add)(start = BookingsTable.holding, observe = _.bookings)(t => (t.inRoom, t.add))

  test("finding 1: always anywhere but as a node's whole formula is refused") {
    val underImplies = Node.claim("Under implies.")(
      forall((b: Term[Booking]) => (b.start < b.end) implies always[Booking](x => x.start < x.end)))
    val negated = Node.claim("Not every booking that can be made ends after it starts.")(
      !always[Booking](x => x.start < x.end))
    val leftOf = Node.claim("Left of implies.")(
      always[Booking](x => x.start < x.end) implies storedBookings.current.isEmpty)
    val storeOr = Node.claim("Store always, or.")(always(storedBookings)(s => s.isEmpty) || True)
    List(underImplies, negated, leftOf, storeOr).foreach(n =>
      assertEquals(faults(FrModel("Rooms")(n)), List(Fault.AlwaysInside), n.head.id.value))
    assertEquals(faults(FrModel("Rooms")(ends)), Nil)
  }

  private val ofRoom = define { (room: Term[String]) => storedBookings.current.filter(b => b.room === room) }

  test("finding 2: a world read unnamed beside a run's world after is refused; named, it reads the world said") {
    val unnamed = Node.claim("Once booked, the request is not among its room's bookings.")(
      forall((r: Term[Booking]) => storedBookings.in(book(r).after).contains(r) implies !ofRoom(r.room).contains(r)))
    assertEquals(faults(withCode(unnamed)), List(Fault.WorldUnnamed(List("ofRoom"))))
    val after = Node.claim("Once stored, the request is among its room's bookings.")(
      forall((r: Term[Booking]) => storedBookings.in(book(r).after).contains(r) implies
        ofRoom(r.room).in(book(r).after).contains(r)))
    val before = Node.claim("Once stored, the request was among its room's bookings or is new.")(
      forall((r: Term[Booking]) => storedBookings.in(book(r).after).contains(r) implies
        (ofRoom(r.room).current.contains(r) || book(r).result)))
    assertEquals(faults(withCode(after, before)), Nil)
    def readAt(id: String) = Exprs.all(formula(withCode(after, before), id)).collect {
      case Expr.Call(d, args, _) if d.value == "ofRoom" => args.last
    }
    assert(readAt("after").nonEmpty && readAt("after").forall {
      case Expr.Var(x) => x.hint == "after"
      case _           => false
    }, readAt("after"))
    assert(readAt("before").nonEmpty && readAt("before").forall {
      case Expr.Var(x) => x.hint == "world"
      case _           => false
    }, readAt("before"))
    val declared = Node.claim("An accepted request is booked after it is handled.")(
      forall((r: Term[Booking]) => accepted(r) implies storedBookings.in(book(r).after).contains(r)))
    assertEquals(faults(withCode(declared, acceptedIsAnswered)), List(Fault.WorldUnnamed(List("accepted"))))
  }

  test("finding 15: a Declaration read beside a run changes with the World, its statement read alone or not") {
    val kb = withCode(acceptedIsAnswered)
    assertEquals(Theories.theory(kb).vocabulary.symbol(SymbolName("accepted")).map(_.ty), Some(
      frflow.core.vocab.SymbolType.Typed(frflow.core.ty.Ty.FnOf(List(frflow.core.ty.Ty.Data(
        frflow.core.name.TypeName("Booking")), frflow.core.ty.Ty.World), frflow.core.ty.Ty.Bool))))
  }

  test("finding 6, owner §45 E: the worlds after two runs in one statement are refused") {
    val two = Node.claim("Booking b after a keeps a.")(
      forall((a: Term[Booking], b: Term[Booking]) =>
        storedBookings.in(book(a).after).contains(a) implies storedBookings.in(book(b).after).contains(a)))
    assertEquals(faults(withCode(two)), List(Fault.AfterOfTwo("book", "book")))
  }

  private val opening = Declaration[BigInt]("the hour the rooms open")

  test("owner §45 A: isConstant where no step keeps it, or of a run, is refused") {
    val negated = Node.claim("The opening hour changes.")(!opening.isConstant)
    val left = Node.claim("If the hour never changes the table is empty.")(
      opening.isConstant implies storedBookings.current.isEmpty)
    val or = Node.claim("Either.")(opening.isConstant || storedBookings.current.isEmpty)
    val condition = Node.claim("In a condition.")(when(opening.isConstant)(True).otherwise(False))
    val ofRun = Node.claim("Of a run.")(forall((r: Term[Booking]) => book(r).result.isConstant))
    List(negated -> "under !", left -> "left of implies", or -> "under ||", condition -> "in a condition",
      ofRun -> "of a run").foreach((n, where) =>
      assertEquals(faults(withCode(n)), List(Fault.ConstantInside(where)), n.head.id.value))
    val conditioned = Node.assumption("Once open, the table's bookings stay.")(
      !storedBookings.current.isEmpty implies storedBookings.current.isConstant)
    assertEquals(faults(withCode(conditioned)), Nil)
  }

  test("owner §45 A: isConstant in an example or a define is refused") {
    class Fixed extends FrFlowExamples(rooms):
      example("the opening hour is fixed")(opening.isConstant)
    assertEquals(Fixed().elaborated.fold(_.iterator.map(_.fault).toList, _ => Nil),
      List(Fault.ConstantInside("in an example")))
    val inDefine = Node.claim("A define of constancy.")(forall((room: Term[String]) =>
      val constancy = define((x: Term[String]) => ofRoom(x).isConstant)
      constancy(room)))
    assert(faults(withCode(inDefine)).contains(Fault.ConstantInside("in a define")), faults(withCode(inDefine)))
    assert(compileErrors("define((x: Term[String]) => ofRoom(x).isConstant)").contains("used only in statements"))
  }

  val store = Definition[BigInt => Flow[Unit]]("a number stored on the shelf").failsWith[Trouble]
  val storeCode = program { (n: Term[BigInt]) => Flow.step(Shelf.put(n)) }
  val shelfOnly = Node.assumption("Nothing but the programs change the shelf.")(Shelf.kept.onlyCodeChanges)
  val shelfOne = Node.assumption("One at a time.")(Shelf.kept.atomic)

  test("owner §44, §45 A: isConstant is one equation per program that changes what it reads, both outcomes") {
    val stays = Node.claim("The shelf stays as it is.")(Shelf.kept.current.isConstant).assuming(shelfOnly, shelfOne)
    val mentioned = Node.claim("Storing a number keeps it.")(
      forall((n: Term[BigInt]) => store(n).result.fold(_ => True,
        _ => Shelf.kept.in(store(n).after).contains(n)))).assuming(shelfOne)
    val kb = FrModel("Shelves")(stays, mentioned, shelfOnly, shelfOne).implementProven(store)(storeCode)
    val programs = Exprs.all(formula(kb, "stays")).collect { case r: Expr.Runs => r.run -> r.failing }.collect {
      case (Expr.Apply(Expr.Sym(n, _), _, _), failing) => n -> failing
    }
    assertEquals(programs, List(SymbolName("store") -> false, SymbolName("store") -> true))
    val written = Theories.theory(kb).node(NodeId("stays")).flatMap(_.statement.said).getOrElse(fail("no stays"))
    assertEquals(Constancy.models(written), List(Shelf.kept.name))
    assertEquals(Theories.problems(kb), Nil)
    val unassumed = Node.claim("The shelf stays as it is.")(Shelf.kept.current.isConstant)
    val missing = Theories.problems(FrModel("Shelves")(unassumed, mentioned).implementProven(store)(storeCode))
    assert(missing.exists {
      case Problem.PremiseMissing(id, Premise.OnlyCodeChanges(m), _) => id == NodeId("unassumed") && m == ModelName(
          Shelf.kept.name.value)
      case _                                                         => false
    }, missing)
  }

  test("owner §45 C, finding 13: a rule over a Declaration that changes with the World is refused") {
    val rule = Node.assumption("Bookings start once open.")(always[Booking](b => opening <= b.start))
    val fixed = Node.assumption("The opening hour never changes.")(opening.isConstant)
    assertEquals(faults(FrModel("Rooms")(rule, fixed)), List(Fault.RuleOverChanging("opening", "rule", "fixed")))
    assertEquals(faults(FrModel("Rooms")(rule)), Nil)
  }

  test("finding 3, owner §46: a program that can fail declares it, and its run is read with both outcomes") {
    val neverStores = program { (n: Term[BigInt]) => Flow.raise[Trouble, Unit](make[Trouble.TooBig](n)) }
    val undeclared = Definition[BigInt => Flow[Unit]]("a number stored on the shelf, failing undeclared")
    val puts = Node.claim("Storing a number puts it on the shelf.")(
      forall((n: Term[BigInt]) => Shelf.kept.in(undeclared(n).after) === Shelf.kept.current :+ n))
    assertEquals(Theories.problems(FrModel("Shelves")(puts, shelfOnly).implementProven(undeclared)(neverStores)),
      List(Problem.FailsWithDiffers(SymbolName("undeclared"), None, List(summon[LeanType[Trouble]].ty))))
    val putsDeclared = Node.claim("Storing a number puts it on the shelf.")(
      forall((n: Term[BigInt]) => Shelf.kept.in(store(n).after) === Shelf.kept.current :+ n))
    val runs = Exprs.all(formula(FrModel("Shelves")(putsDeclared, shelfOnly).implementProven(store)(neverStores),
      "putsDeclared")).collect { case r: Expr.Runs => r.failing }
    assertEquals(runs, List(false, true))
    val never = program { (n: Term[BigInt]) => Flow.step(Shelf.put(n)).handle[Trouble](_ => Flow.unit) }
    val neverProblems = Theories.problems(FrModel("Shelves")(putsDeclared, shelfOnly).implementProven(store)(never))
    assert(neverProblems.contains(Problem.FailsWithDiffers(SymbolName("store"), Some(summon[LeanType[Trouble]].ty),
      Nil)), neverProblems)
    val result: Term[Either[Trouble, Unit]] = store(5).result
    assert(Term.exprOf(result).nonEmpty)
  }

  test("finding 8, owner §45 D: no port reads a value provided where the code runs beside the World") {
    List(rooms, auth.knowledge, crm.knowledge, keycloak.knowledge).foreach(kb =>
      assertEquals(frflow.core.analysis.Validate.providedBesideWorld(Theories.theory(kb)), Nil, kb.name.value))
  }

  test("finding 10: an example whose value breaks a rule on its type is refused, not judged on the code") {
    class Overlapping extends FrFlowExamples(rooms):
      example("overlapping held: granted"):
        granted(RoomBookings("Oak", List(Booking("Oak", 9, 11), Booking("Oak", 10, 12))), Booking("Oak", 12, 13)) is
          true
    val e = Theories.elaborated(rooms)
    val run = ExampleRun(Semantics(e), e.theory)
    assertEquals(Overlapping().elaborated.fold(es => fail(es.iterator.mkString), identity).map(run.of),
      List(OnCode.BreaksRule(NodeId("roomBookingsApart"))))
  }

  test("finding 7: a claim reading a run has its condition asked, of the run that gives what it reads") {
    val j = Node.claim("A request answered booked is stored.")(
      forall((r: Term[Booking]) => book(r).result implies storedBookings.in(book(r).after).contains(r)))
    assert(Consistency.vacuity(Theories.theory(withCode(j))).exists {
      case Vacuity.Satisfiable(n, _, _) => n == NodeId("j")
      case _                            => false
    })
  }
