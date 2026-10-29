package rooms

import frflow.*
import frflow.core.expr.{Expr, Exprs, Quantifier}
import frflow.core.name.SymbolName
import frflow.core.ty.Ty
import frflow.core.vocab.SymbolType
import frflow.dsl.build.Fault
import whole.Theories

/** The World implicit in statements (owner §41, §43): a statement holds in every reachable world, reading what
  * changes
  * with it in the current one; which Declarations change with it is read off the statements, as is which defines;
  * `isConstant` says one is the same in every world.
  */
class WorldSuite extends munit.FunSuite:
  private def typeOf(kb: FrModel, n: String): Option[Ty] =
    Theories.theory(kb).vocabulary.symbol(SymbolName(n)).map(_.ty).collect { case SymbolType.Typed(t) => t }

  test("rooms' Declarations change with the World, read beside the table: a function of the world, its last input") {
    assertEquals(typeOf(_root_.rooms.rooms, "booked"), Some(Ty.FnOf(List(Ty.World), Ty.ListOf(Ty.Data(
      frflow.core.name.TypeName("Booking"))))))
    assertEquals(typeOf(_root_.rooms.rooms, "accepted").map { case Ty.FnOf(ins, _) => ins.last; case t => t },
      Some(Ty.World))
  }

  test("a Declaration no statement reads beside what changes is a value in Lean, as auth's and crm's are") {
    assertEquals(typeOf(auth.knowledge, "access").map { case Ty.FnOf(ins, _) => ins.contains(Ty.World); case _ => true
      }, Some(false))
    assertEquals(typeOf(crm.knowledge, "finds").map { case Ty.FnOf(ins, _) => ins.contains(Ty.World); case _ => true },
      Some(false))
  }

  test("a statement reading the world binds it once, below its leading variables; one reading none is as written") {
    def quantified(e: Expr): List[Ty] = e match
      case Expr.Quant(Quantifier.Forall, List(x), body) => x.ty :: quantified(body)
      case _                                           => Nil
    val stored = Theories.theory(_root_.rooms.rooms).nodes.map(_.node).find(_.id.value == "storeWhenFree").get
    assertEquals(stored.statement.said.map(f => quantified(f.value)), Some(List(Ty.Data(
      frflow.core.name.TypeName("Booking")), Ty.World)))
    val grant = Theories.theory(_root_.rooms.rooms).nodes.map(_.node).find(_.id.value == "grantWhenFree").get
    assert(grant.statement.said.exists(f => !quantified(f.value).contains(Ty.World)))
  }

  test("isConstant: of a Declaration changing with the World, the same in every two worlds; of another, itself") {
    val holds = Node.claim("What is booked is what the table holds.")(booked === storedBookings.current)
    val fixed = Node.assumption("What is booked never changes.")(booked.isConstant)
    val kb = FrModel("Rooms")(holds, fixed)
    val worlds = Theories.theory(kb).nodes.map(_.node).find(_.id.value == "fixed").flatMap(_.statement.said)
      .map(f => Exprs.all(f.value).collect { case Expr.Quant(_, List(x), _) if x.ty == Ty.World => x }.size)
    assertEquals(worlds, Some(2))
    val alone = RoomsIr.formula(Node.assumption("What is booked never changes.")(booked.isConstant).alone)
    assert(Exprs.all(alone).forall { case Expr.Quant(_, _, _) => false; case _ => true }, alone)
  }

  test("a define reading state changes with the World: it takes the world last, its calls read it where they are") {
    val ofRoom = define { (room: Term[String]) => storedBookings.current.filter(b => b.room === room) }
    assert(ofRoom.readsWorld)
    assertEquals(RoomsIr.lambda(ofRoom).value.params.map(_.ty), List(Ty.Str, Ty.World))
    val heldOf = Node.claim("A room's bookings are of it.")(
      forall((room: Term[String]) => ofRoom(room).forall(b => b.room === room)))
    val worlds = Theories.theory(FrModel("Rooms")(heldOf)).nodes.head.node.statement.said
      .map(f => Exprs.all(f.value).collect { case Expr.Quant(_, List(x), _) if x.ty == Ty.World => x }.size)
    assertEquals(worlds, Some(1))
    val itself = define { (room: Term[String]) => room === room }
    assert(!itself.readsWorld)
  }

  test("a run is of the statement's own variables; the world is not read where nothing holds one") {
    def faults(n: frflow.dsl.node.Node) = n.alone.run.fold(_.iterator.map(_.fault).toList, _ => Nil)
    assertEquals(faults(Node.claim("Every request in a list is booked.")(
      forall((rs: Term[List[Booking]]) => rs.forall(r => book(r).result)))), List(Fault.RunInside("book")))
    val rule = Node.claim("Every booking is stored.")(always[Booking](b => storedBookings.current.contains(b)))
    assert(faults(rule).exists { case Fault.WorldRead(_) => true; case _ => false }, faults(rule))
  }
