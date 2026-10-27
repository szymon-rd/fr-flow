package frflow.testing

import frflow.*
import frflow.core.example.Gen
import frflow.core.expr.Value
import frflow.core.name.NodeId
import frflow.eval.Semantics
import frflow.eval.run.Broken
import frflow.testing.derive.Derive
import frflow.testing.report.{Against, Count, Failure, Made, Outcome, Reach, TestReport}
import frflow.testing.Shelf.*
import java.util.SplittableRandom

/** Plain code tested against the claims on its Definition (today's `TestingSuite`, its case names kept): the
  * property is the claim's formula, the cases drawn from the types.
  */
class TestingSuite extends munit.FunSuite:
  private val few = Settings(300, Seed(3))
  private def tested(kb: FrModel, node: String = "pick", settings: Settings = few,
      replay: List[Failure] = Nil): Option[TestReport] =
    val e = kb.elaborated.fold(es => fail(es.iterator.mkString("\n")), identity)
    PropertyTests(Semantics(e), e.theory).of(NodeId(node), Plan(settings, replay), Derive.of(e, Nil))
  private def failing(kb: FrModel, node: String = "pick"): Failure.Call =
    tested(kb, node).flatMap(_.failure).collect { case f: Failure.Call => f }.getOrElse(fail("the bug was not found"))
  private val offByOne = withCode(min => (shelf, _) => shelf.filter(_.pages > min))

  test("code that meets its contract passes, and every part of the contract is reached") {
    val r = tested(kb).getOrElse(fail("pick is not tested"))
    assertEquals((r.failure, r.unreached, r.against, r.cases), (None, Nil, Against.Claim(NodeId("pick")), 300))
    val e = kb.elaborated.fold(es => fail(es.toString), identity)
    val counted = Coverage(Semantics(e), e.theory, NodeId("pick"), List(LeanType[List[Book]].ty, LeanType[BigInt].ty))
    assertEquals(counted.zero.counts.keySet.map(_.reach), Set(Reach.NonEmpty, Reach.Premise))
    assertEquals(counted.zero.counts.size, 3)
  }

  test("FRFLOW_SEED replaces the seed: a number, or fresh; anything else keeps the settings") {
    val (s, fresh) = (Settings(50, Seed(3)), Seed(77))
    assertEquals(Settings.withSeed(s, Some("42"), fresh), s.copy(seed = Seed(42)))
    assertEquals(Settings.withSeed(s, Some("fresh"), fresh), s.copy(seed = fresh))
    assertEquals(Settings.withSeed(s, Some("soon"), fresh), s)
    assertEquals(Settings.withSeed(s, None, fresh), s)
    assertEquals(Settings.default, Settings(1000, Seed(1)))
  }

  test("a seeded bug is found, and the case is shrunk to its smallest") {
    val f = failing(offByOne)
    // One book, at the length asked, the rest as small as the shrinker goes; the length given as minPages.
    f match
      case Failure.Call(List(Value.Many(List(Value.Data(_, List(Value.Str(""), Value.Num(pages))))), Value.Num(n)),
          List(asked), Broken.Post, _) =>
        assertEquals((n, asked.value, asked.symbol), (BigInt(0), Value.Num(pages), minPages.name))
      case other => fail(s"not shrunk: $other")
  }

  test("the same seed gives the same cases; a failing case replays first") {
    val (a, b) = (failing(offByOne), failing(offByOne))
    assertEquals(a, b)
    // Replayed (even under another seed), the case that failed is the first one tried.
    val again = tested(offByOne, settings = Settings(300, Seed(99)), replay = List(a)).flatMap(_.failure)
    assertEquals(again.map(_.from), Some(a.from))
    assertEquals(tested(offByOne, settings = Settings(300, Seed(99)), replay = List(a)).map(_.cases), Some(1))
  }

  test("a part no case reaches is said, not passed") {
    // Every book is short and the length asked 100: `b.pages >= minPages implies …` never holds its premise.
    val short = new Draw:
      def apply[A](g: Gen[A], size: Int, random: SplittableRandom): Option[A] = None
      override def all(types: List[frflow.core.ty.Ty], size: Int, random: SplittableRandom): Option[List[Any]] =
        Some(List(List(Book("Short", 1)), BigInt(random.nextInt(3)), BigInt(100)))
    val e = kb.elaborated.fold(es => fail(es.toString), identity)
    val r = PropertyTests(Semantics(e), e.theory).of(NodeId("pick"), Plan(few, Nil), short)
    assertEquals(r.map(_.failure), Some(None))
    // Nothing is picked from a shelf of short books, and no book is long enough.
    assertEquals(r.toList.flatMap(_.unreached).map(_.reach), List(Reach.NonEmpty, Reach.Premise))
  }

  test("a run that draws nothing tries nothing, and says so: every part unreached") {
    val nothing = new Draw:
      def apply[A](g: Gen[A], size: Int, random: SplittableRandom): Option[A] = None
    val e = kb.elaborated.fold(es => fail(es.toString), identity)
    val r = PropertyTests(Semantics(e), e.theory).of(NodeId("pick"), Plan(few, Nil), nothing)
      .getOrElse(fail("pick is not tested"))
    assertEquals((r.count, r.count.shortfall, r.outcome, r.unreached.size), (Count(300, 0), 300, Outcome.Passed, 3))
  }

  test("a given generator is said in the report, with what the developer said it makes") {
    val narrow = kb.generating(Gen.oneOf(Book("A", 1), Book("B", 2)).describedAs("two short books"))
    assertEquals(tested(narrow).map(_.made), Some(List(Made(LeanType[Book].ty, Some("two short books")))))
  }

  test("generated values cover the types: numbers, strings, lists, options, enums") {
    val e = FrModel("Places")(Node.claim("A place is itself.")(forall((p: Term[Place]) => p === p)))
      .elaborated.fold(es => fail(es.toString), identity)
    val d = Derive.of(e, Nil)
    val places = (0 until 200).flatMap(i => d(Gen.Derived[Place](LeanType[Place].ty), 6, Seed(5).forCase(i)))
    assert(List("Top", "Bottom", "Box").forall(c => places.exists(_.toString.startsWith(c))), places.distinct)
    val maybes = (0 until 200).flatMap(i => d(Gen.Derived[Option[Long]](LeanType[Option[Long]].ty), 6,
      Seed(5).forCase(i)))
    assert(maybes.contains(None) && maybes.exists(_.exists(_ != 0L)), maybes.distinct)
    assertEquals(d(Gen.Derived[BigInt => Boolean](LeanType[BigInt => Boolean].ty), 3, Seed(5).forCase(0)), None)
  }

  test("a proven define has nothing to test") {
    val proven = FrModel("Shelf")(pick).implementProvided(minPages)
      .implementProven(picks)(define((shelf: Term[List[Book]], _: Term[BigInt]) =>
        shelf.filter(b => b.pages >= minPages)))
    assertEquals(tested(proven), None)
  }

  test("one input: a generated test finds a bug and shrinks it") {
    val wrong = FrModel("Shelf")(noLonger)
      .implementTested(longest)(_ => shelf => shelf.headOption.fold(BigInt(0))(_.pages))
    assertEquals(failing(wrong, "noLonger").inputs.map(shrunkBooks), List(2))
  }

  test("three inputs: a generated test finds a bug and shrinks it") {
    val wrong = FrModel("Shelf")(inRange).implementTested(between)(_ => (shelf, lo, _) =>
      shelf.filter(_.pages >= lo))
    val f = failing(wrong, "inRange")
    assertEquals((f.inputs.size, f.broke), (3, Broken.Post))
    assertEquals(f.inputs.headOption.map(shrunkBooks), Some(1))
  }

  test("no input: a generated test under the values given finds a bug and shrinks it") {
    val wrong = FrModel("Shelf")(todayLong).implementProvided(minPages)
      .implementTested(today)(_ => List(Book("Short", 1)))
    val f = failing(wrong, "todayLong")
    assertEquals((f.inputs, f.givens.map(_.value)), (Nil, List(Value.Num(2))))
  }

  test("the implementation is tested beyond its examples: a case that breaks the contract is found, " +
      "code that throws too") {
    val throws = withCode(min => (shelf, _) =>
      if shelf.size > 1 then sys.error("too many") else shelf.filter(_.pages >= min))
    assertEquals(failing(throws).broke, Broken.Threw("too many"))
    assertEquals(failing(throws).inputs.headOption.map(shrunkBooks), Some(2))
  }

  /** How many books a shrunk shelf holds. */
  private def shrunkBooks(v: Value): Int = v match
    case Value.Many(xs) => xs.size
    case _              => -1
