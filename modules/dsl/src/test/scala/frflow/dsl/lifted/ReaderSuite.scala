package frflow.dsl.lifted

import frflow.core.expr.{Expr, Iteration, PrimOp, Quantifier}
import frflow.core.ty.{NumKind, Ty}
import frflow.dsl.lifted.LiftSyntax.{contractOf, lifted}
import frflow.dsl.vocab.Definition

/** What the reader reads of Scala's standard types, each as the IR's own operation; a type's contract in plain
  * Scala; and a closed fact.
  */
class ReaderSuite extends munit.FunSuite:
  private val big = Ty.Num(NumKind.Big)

  private def body(d: Definition[?]): Expr =
    d.onTheSpot.fold(fail(s"${d.name} has no meaning where it is written"))(_.lambda.run.fold(
      es => fail(es.toChain.toList.mkString("; ")), _._2.value.body))

  private def prim(d: Definition[?]): (PrimOp, Ty) = body(d) match
    case Expr.Prim(op, _, ty) => (op, ty)
    case other                => fail(s"not an operator: $other")

  private def iterated(d: Definition[?]): (Iteration, Ty) = body(d) match
    case Expr.Iterate(how, _, _, _, ty) => (how, ty)
    case other                          => fail(s"not an iteration: $other")

  test("a list written out, the empty list, cons, append and length") {
    val twice = lifted { (x: BigInt) => List(x, x) }
    val none = lifted { (x: BigInt) => if x < BigInt(0) then Nil else x :: Nil }
    val both = lifted { (xs: List[BigInt], ys: List[BigInt]) => BigInt((xs ++ ys).length) }
    assertEquals(prim(twice), (PrimOp.Cons, Ty.ListOf(big)))
    assert(body(none).isInstanceOf[Expr.If], body(none).toString)
    assertEquals(prim(both), (PrimOp.Length, big))
  }

  test("a list's exists, find, flatMap, contains and nonEmpty") {
    val any = lifted { (xs: List[BigInt]) => xs.exists(x => x < BigInt(0)) }
    val first = lifted { (xs: List[BigInt]) => xs.find(x => x < BigInt(0)) }
    val pairs = lifted { (xs: List[BigInt]) => xs.flatMap(x => List(x, x)) }
    val has = lifted { (xs: List[BigInt], x: BigInt) => xs.contains(x) && xs.nonEmpty }
    assertEquals(iterated(any), (Iteration.Exists, Ty.Bool))
    assertEquals(iterated(first), (Iteration.Find, Ty.OptionOf(big)))
    assertEquals(iterated(pairs), (Iteration.FlatMap, Ty.ListOf(big)))
    assertEquals(prim(has)._1, PrimOp.And)
  }

  test("an option made, asked and folded") {
    val some = lifted { (x: BigInt) => if x < BigInt(0) then None else Some(x) }
    val orZero = lifted { (o: Option[BigInt]) => o.getOrElse(BigInt(0)) }
    val positive = lifted { (o: Option[BigInt]) => o.forall(x => BigInt(0) < x) && o.isDefined }
    val next = lifted { (o: Option[BigInt]) => o.map(x => x + BigInt(1)).fold(BigInt(0))(x => x) }
    assert(body(some).isInstanceOf[Expr.If], body(some).toString)
    assertEquals(prim(orZero), (PrimOp.GetOrElse, big))
    assertEquals(prim(positive)._1, PrimOp.And)
    assert(body(next).isInstanceOf[Expr.Match], body(next).toString)
  }

  test("a map's value at a key, a set's member, a pair's sides") {
    val at = lifted { (m: Map[String, BigInt], k: String) => m.getOrElse(k, BigInt(0)) }
    val put = lifted { (m: Map[String, BigInt], k: String) => m.updated(k, BigInt(1)).contains(k) }
    val in = lifted { (s: Set[String], x: String) => (s + x).contains(x) }
    val swap = lifted { (p: (String, BigInt)) => (p._2, p._1) }
    assertEquals(prim(at), (PrimOp.GetOrElseAt, big))
    assertEquals(prim(put), (PrimOp.NonEmpty, Ty.Bool))
    assertEquals(prim(in), (PrimOp.Contains, Ty.Bool))
    assertEquals(body(swap).getClass, classOf[Expr.Tuple])
  }

  test("an enum's case made is a value of the enum where one is used") {
    val unit = lifted { (r: BigInt) => if r < BigInt(1) then Shape.Empty else Shape.Circle(r) }
    val widest = lifted { (s: Shape) =>
      s match
        case c: Shape.Circle => c.radius
        case Shape.Rect(w, _) => w
        case Shape.Empty      => BigInt(0) }
    assert(body(unit).isInstanceOf[Expr.If], body(unit).toString)
    assert(body(widest).isInstanceOf[Expr.Match], body(widest).toString)
  }

  test("a type's contract in plain Scala is the rule a node states, and checks a value where the code runs") {
    val spec = FrSpec.derived[Booking].where(b => b.start < b.end)
    val everyBookingEnds = contractOf[Booking](using spec)
    assert(spec.holds(Booking("Oak", 9, 10)))
    assert(!spec.holds(Booking("Oak", 10, 10)))
    everyBookingEnds.expr match
      case Expr.Quant(Quantifier.Always, List(x), Expr.Call(rule, _, _)) =>
        assertEquals((x.ty, rule.value), (Ty.Data(frflow.core.name.TypeName("Booking")), "everyBookingEnds"))
      case other                                                        => fail(s"not a rule: $other")
  }

  test("a contract over a member that is an inline method") {
    val spec = FrSpec.derived[Booking].where(b => BigInt(0) < b.length)
    assert(spec.holds(Booking("Oak", 9, 10)) && !spec.holds(Booking("Oak", 10, 9)))
    val everyBookingLasts = contractOf[Booking](using spec)
    assertEquals(everyBookingLasts.notes.faults.toList, Nil)
  }

  test("a type whose spec states no contract has none to state: a fault on the node") {
    val nothing = contractOf[RoomBookings]
    assertEquals(nothing.notes.faults.toList.map(_.toString), List("NoContract(RoomBookings)"))
  }

  test("a closed fact in plain Scala is its term: lifted functions called on values written out") {
    val noOverlap = lifted { (a: Booking, b: Booking) => a.room != b.room || a.end <= b.start || b.end <= a.start }
    val fact = lifted { noOverlap(Booking("Oak", BigInt(9), BigInt(10)), Booking("Oak", BigInt(10), BigInt(11))) }
    fact.expr match
      case Expr.Call(name, List(_: Expr.Make, _: Expr.Make), Ty.Bool) => assertEquals(name.value, "noOverlap")
      case other                                                      => fail(s"not a call: $other")
  }
