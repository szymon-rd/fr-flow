package rooms

import frflow.*
import frflow.core.expr.{Expr, Exprs}
import frflow.core.name.SymbolName
import frflow.core.ty.{NumKind, Ty}
import frflow.core.vocab.SymbolType
import frflow.dsl.build.Fault
import frflow.eval.flow.{Shelf, Trouble}
import whole.Theories

/** Where reading the World is refused or made explicit (owner §41, §43): `isConstant` makes its Declaration one that
  * changes with the World; a rule reads its Declarations as values, which an `isConstant` assumption must say; one
  * program's run is read one way in a statement; a store rule, like a value rule, reads no state; an example reads no
  * world; a run read as failing states its failing side.
  */
class WorldRulesSuite extends munit.FunSuite:
  private def typeOf(kb: FrModel, n: String): Option[Ty] =
    Theories.theory(kb).vocabulary.symbol(SymbolName(n)).map(_.ty).collect { case SymbolType.Typed(t) => t }
  private def faults(kb: FrModel): List[Fault] = Theories.errors(kb).map(_.fault)
  private def worlds(e: Expr): Int = Exprs.all(e).count {
    case Expr.Quant(_, List(x), _) => x.ty == Ty.World
    case _                         => false
  }
  private def formula(kb: FrModel, id: String): Expr =
    Theories.theory(kb).nodes.map(_.node).find(_.id.value == id).flatMap(_.statement.said).map(_.value)
      .getOrElse(fail(s"no $id"))
  private val hour = Ty.Num(NumKind.Big)

  val opening = Declaration[BigInt]("the hour the rooms open")
  val openingFixed = Node.claim("The opening hour never changes.")(opening.isConstant)
  val openingAssumed = Node.assumption("The opening hour never changes.")(opening.isConstant)
  val startsOpen = Node.claim("Every stored booking starts once the rooms are open.")(
    always(storedBookings)(stored => stored.forall(b => opening <= b.start)))
  val bookedOpen = Node.claim("Every booking held starts once the rooms are open.")(
    storedBookings.current.forall(b => opening <= b.start))

  test("isConstant reads the World: claimed alone, the Declaration is a function of it, the same in every two") {
    assertEquals(typeOf(FrModel("Rooms")(openingFixed), "opening"), Some(Ty.FnOf(List(Ty.World), hour)))
    assertEquals(worlds(formula(FrModel("Rooms")(openingFixed), "openingFixed")), 2)
  }

  test("a rule reads its Declarations as values: refused unless an assumption says each never changes") {
    assertEquals(faults(FrModel("Rooms")(startsOpen)), List(Fault.RuleOverChanging("opening", "startsOpen")))
    assertEquals(faults(FrModel("Rooms")(startsOpen, openingFixed)),
      List(Fault.RuleOverChanging("opening", "startsOpen")))
    val assumed = FrModel("Rooms")(startsOpen, openingAssumed, bookedOpen)
    assertEquals(faults(assumed), Nil)
    assertEquals(typeOf(assumed, "opening"), Some(hour))
    assertEquals(worlds(formula(assumed, "openingAssumed")), 0)
  }

  val store = Definition[BigInt => Flow[Unit]]("a number stored on the shelf")
  val storeCode = program { (n: Term[BigInt]) => Flow.step(Shelf.put(n)) }
  private def shelf(c: frflow.dsl.node.Node): FrModel = FrModel("Shelves")(c).implementProven(store)(storeCode)

  test("a run read both as failing and plainly in one statement is refused: the plain reading says nothing failing") {
    val mixed = Node.claim("A store that fails leaves the shelf holding the number twice more.")(
      forall((n: Term[BigInt]) => store(n).failing[Trouble].result.fold(
        _ => Shelf.kept.in(store(n).after) === Shelf.kept.current :+ n :+ n, _ => n === n)))
    assertEquals(faults(shelf(mixed)), List(Fault.ReadTwoWays("store")))
  }

  test("a run read as failing states its failing side: the world a failed run leaves, beside the one it succeeds in") {
    val failed = Node.claim("A store that fails leaves the shelf as it was.")(
      forall((n: Term[BigInt]) => store(n).failing[Trouble].result.fold(
        _ => Shelf.kept.in(store(n).failing[Trouble].after) === Shelf.kept.current, _ => n === n)))
    formula(shelf(failed), "failed") match
      case Expr.Quant(_, _, Expr.Quant(_, _, Expr.Prim(_, List(ok: Expr.Runs, err: Expr.Runs), _))) =>
        assertEquals((ok.failing, err.failing), (false, true))
        assert(Exprs.all(err.post).exists { case Expr.Part(Expr.Var(a), _, _) => a == err.after; case _ => false },
          err.post)
      case other => fail(other.toString)
  }

  test("a store rule reading state is refused, as a value rule is") {
    val heldNow = Node.claim("The table holds what the table holds.")(
      always(storedBookings)(stored => stored === storedBookings.current))
    assert(faults(FrModel("Rooms")(heldNow)).exists { case Fault.WorldRead(_) => true; case _ => false },
      faults(FrModel("Rooms")(heldNow)))
  }

  test("an example reads no world: one over a Declaration that changes with the World is refused, no FrFlow bug") {
    class Varying extends FrFlowExamples(rooms):
      example("what is booked is itself")(booked === booked)
      example("back to back: granted"):
        granted(RoomBookings("Oak", List(Booking("Oak", 9, 10))), Booking("Oak", 10, 11)) is true
    assertEquals(Varying().elaborated.fold(_.iterator.map(_.fault).toList, _ => Nil),
      List(Fault.WorldRead("an example")))
  }
