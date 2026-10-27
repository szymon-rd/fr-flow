package rooms

import frflow.*
import frflow.core.example.Gen
import frflow.testing.Seed
import frflow.eval.{ScalaValue, Semantics}
import frflow.testing.derive.{Always, Derive, Hints, Seeds}

/** Drawn values meet their fields' rules (step 5, section 10.2): a `RoomBookings` drawn by its type, from the derived
  * generators alone, meets `endsAfterStart` for each booking it holds, and the rules on itself.
  */
class DrawnSuite extends munit.FunSuite:
  /** Rooms without the generators it gives: every value derived from its type. */
  private val derivedOnly = rooms.copy(generators = Nil)
  private def derive(kb: FrModel) = Derive.of(kb.elaborated.fold(es => fail(es.toString), identity), Nil)
  private def drawn(d: Derive, n: Int): List[RoomBookings] = (0 until n).toList.flatMap(i =>
    d(Gen.Derived[RoomBookings](LeanType[RoomBookings].ty), Seed.sizeOf(i, n), Seed(1).forCase(i)))

  test("a drawn RoomBookings meets endsAfterStart for each booking it holds, with nothing given to draw it from") {
    val all = drawn(derive(derivedOnly), 300)
    assert(all.size > 250, s"${all.size} of 300 drawn")
    val bookings = all.flatMap(_.bookings)
    assert(bookings.size > 100, s"${bookings.size} bookings drawn")
    assert(bookings.forall(b => b.start < b.end), bookings.filterNot(b => b.start < b.end).take(3))
  }

  test("and the rules on RoomBookings itself: every booking of its room, none overlapping another") {
    val all = drawn(derive(derivedOnly), 300)
    assert(all.forall(r => r.bookings.forall(_.room == r.room)), all.find(r => r.bookings.exists(_.room != r.room)))
    def apart(a: Booking, b: Booking) = a.end <= b.start || b.end <= a.start
    assert(all.forall(r => r.bookings.combinations(2).forall { case List(a, b) => apart(a, b); case _ => true }))
    assert(all.count(_.bookings.size >= 2) >= 10, s"${all.count(_.bookings.size >= 2)} of 300 hold two bookings")
  }

  test("every shape Guards walks: an option's value, an either's side, a pair's component, an enum case's field") {
    val changes = Node.claim("Every change is itself.")(forall((c: Term[Change]) => c === c))
    val d = derive(derivedOnly.copy(nodes = derivedOnly.nodes :+ changes))
    def all[A: LeanType](holding: A => List[Booking]): List[Booking] = (0 until 300).toList.flatMap(i =>
      d(Gen.Derived[A](LeanType[A].ty), Seed.sizeOf(i, 300), Seed(2).forCase(i)).toList.flatMap(holding))
    val held = List(all[Option[Booking]](_.toList), all[Either[String, Booking]](_.toOption.toList),
      all[(Booking, String)](p => List(p._1)), all[Change] { case Change.Book(b) => List(b); case _ => Nil },
      all[List[List[Booking]]](_.flatten))
    held.foreach { bs =>
      assert(bs.size > 20, s"${bs.size} bookings drawn")
      assert(bs.forall(b => b.start < b.end), bs.filterNot(b => b.start < b.end).take(3))
    }
  }

  test("the examples' values are drawn among the derived ones") {
    val examples = GrantedExamples().elaborated.fold(es => fail(es.toString), identity)
    val e = derivedOnly.elaborated.fold(es => fail(es.toString), identity)
    val d = Derive.of(e, examples)
    val bookings = (0 until 300).flatMap(i => d(Gen.Derived[Booking](LeanType[Booking].ty), 3, Seed(4).forCase(i)))
    assert(bookings.contains(Booking("Oak", 9, 10)), bookings.distinct.take(10))
  }

  test("an example's value breaking a rule nested in it is never drawn: a booking ending before it starts") {
    val e = derivedOnly.elaborated.fold(es => fail(es.toString), identity)
    val semantics = Semantics(e)
    val ty = LeanType[RoomBookings].ty
    val bad = semantics.reflect(ScalaValue(RoomBookings("Oak", List(Booking("Oak", 5, 3)))), ty)
    val d = Derive(semantics, e.theory.vocabulary, Always.of(semantics, e.theory),
      Hints(Nil, Seeds(Map(ty -> Vector(bad)), Vector.empty)))
    val bookings = (0 until 300).toList.flatMap(i =>
      d(Gen.Derived[RoomBookings](ty), Seed.sizeOf(i, 300), Seed(1).forCase(i)).toList.flatMap(_.bookings))
    assert(bookings.nonEmpty && bookings.forall(b => b.start < b.end), bookings.filterNot(b => b.start < b.end))
  }

  test("a drawn world's table meets what always holds of the store: no two bookings of a room overlap") {
    val d = derive(derivedOnly)
    val worlds = (0 until 300).toList.flatMap(i => d.values(List(frflow.core.ty.Ty.World), Seed.sizeOf(i, 300),
      Seed(1).forCase(i)).toList.flatten)
    val semantics = Semantics(derivedOnly.elaborated.fold(es => fail(es.toString), identity))
    val tables = worlds.collect { case frflow.core.expr.Value.World(states, _) => states.toMap }
      .flatMap(_.get(storedBookings.name))
      .map(v => frflow.eval.Fn.as[List[Booking]](semantics.literal(v, LeanType[List[Booking]].ty)))
    assert(tables.size == 300 && tables.exists(_.size >= 2), tables.take(5))
    assert(tables.forall(_.combinations(2).forall { case List(a, b) =>
      a.room != b.room || a.end <= b.start || b.end <= a.start; case _ => true }), tables.take(5))
  }

  test("the same seed, case and size draw the same value; another case another") {
    val d = derive(derivedOnly)
    val ty = LeanType[RoomBookings].ty
    assertEquals(d(Gen.Derived[RoomBookings](ty), 5, Seed(3).forCase(7)), d(Gen.Derived[RoomBookings](ty), 5,
      Seed(3).forCase(7)))
    assert(drawn(d, 50).distinct.size > 10)
  }

  test("a type with a generator given is drawn from it three times in four, the rest derived") {
    val all = drawn(derive(rooms), 400)
    val laidEndToEnd = all.count(r => r.bookings.zip(r.bookings.drop(1)).forall((a, b) => a.end <= b.start) &&
      r.bookings.headOption.forall(_.start >= 0) && Set("Oak", "Elm")(r.room))
    assert(laidEndToEnd > 250 && laidEndToEnd < 400, s"$laidEndToEnd of ${all.size} as the given generator lays them")
  }
