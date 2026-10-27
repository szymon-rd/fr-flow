package rooms

import frflow.*
import frflow.core.analysis.{Guards, Resolve, Validate}
import frflow.core.code.Values
import frflow.core.example.Gen
import frflow.core.name.{DefName, KbName, NodeId}
import frflow.core.term.Sym
import frflow.core.ty.Ty
import frflow.eval.run.{Broken, Made}
import frflow.eval.{Env, ScalaValue, Semantics}
import frflow.proof.lean.ast.Names
import frflow.proof.lean.lower.{LowerEnv, Naming}
import frflow.proof.lean.print.Print
import frflow.proof.lean.term.Printed
import frflow.proof.obligation.Required
import frflow.testing.{Draw, Respecting}
import java.util.SplittableRandom

/** `always[T]` reaches every `T` a value holds (owner §16), wherever `Scope.holds` finds one: inside an option, an
  * `Either`, a pair and an enum's case, as inside a list and a record. For each shape, a proven define building a
  * booking end first inside it owes `made_` and breaks `endsAfterStart`; a variable of it comes with the rule in Lean;
  * and a generated value of it meets the rule.
  */
class ShapesSuite extends munit.FunSuite:
  private val bad = Booking("Oak", 11, 9)
  private val good = Booking("Oak", 9, 11)
  private val env = LowerEnv(KbName("Rooms"), _ => Nil, _ => Names.builtin("store"), _ => Names.builtin("Bookings"),
    _ => None)
  private val naming = Naming.over(Set("granted", "book"), Set("Booking", "World"))

  private val maybeMoved = Definition[Request => Option[Booking]]("the booking a request may be moved to")
  private val endFirstMaybe = define { (r: Term[Request]) => some(make[Booking](r.room, r.end, r.start)) }
  private val eitherMoved = Definition[Request => Either[String, Booking]]("where a request is moved, or why not")
  private val endFirstEither = define { (r: Term[Request]) =>
    right[String, Booking](make[Booking](r.room, r.end, r.start)) }
  private val pairMoved = Definition[Request => (Booking, String)]("the booking a request is moved to, with its room")
  private val endFirstPair = define { (r: Term[Request]) =>
    Term.both(make[Booking](r.room, r.end, r.start), r.room)([T[_]] => (s: Sym[T]) => s.pair[Booking, String]) }
  private val changeMoved = Definition[Request => Change]("the change a request is moved by")
  private val endFirstChange = define { (r: Term[Request]) => make[Change.Book](make[Booking](r.room, r.end, r.start)) }

  /** Rooms with a Definition proven by `code`, which a claim about each request mentions. */
  private def shaped[A: LeanType](d: Definition[Request => A], code: Definition[Request => A], tested: Node) =
    val about = Node.claim(s"${d.name.value} is determined by the request.")(
      forall((r: Term[Request]) => d(r) === d(r))).assuming(fromTheForm)
    val kb = KnowledgeBase("Rooms")((rooms.nodes ++ List(about, tested))*).implementProven(book)(bookIfGranted)
      .implementProven(d)(code).implementTested(granted)(_ => (held, request) => Calendar(held).grants(request))
    kb.elaborated.fold(es => fail(es.toString), identity)

  /** What each shape owes and shows: the `made_` of its maker, the rule on a variable of it in Lean, the maker's
    * result breaking the rule in Scala, and a generated value of it meeting the rule.
    */
  private def check(e: frflow.core.Elaborated, maker: String, code: String, ty: Ty, tested: String,
      badValue: Any, goodValue: Any) =
    val r = Resolve(Validate(e).fold(ps => fail(ps.toString), identity))
    val made = Required.made(r, NodeId("endsAfterStart")).map(_.name.toString)
    val claim = r.theory.node(NodeId(tested)).flatMap(_.statement.said).map(f =>
      Print.expr(Printed.claim(env, naming, Guards.of(r.theory))(f.term)))
    val semantics = Semantics(e)
    val rule = Made.of(semantics, e.theory).filter(_.always.value == "endsAfterStart")
    val result = e.theory.vocabulary.define(DefName(code)).toRight("no define").flatMap(d =>
      semantics.lambda(d.written).run(Env.of(Values.none), List(ScalaValue(Request("Oak", 9, 11)))))
    def broken(v: Any) = rule.flatMap(_.broken(List(ScalaValue(v)), List(ty), Env.of(Values.none)))
    val draws = Iterator(badValue, goodValue)
    val drawn = Respecting(new Draw:
      def apply[A](g: Gen[A], size: Int, random: SplittableRandom): A = draws.next().asInstanceOf[A]
    , rule, tries = 2)(Gen.Derived[Any](ty), 1, SplittableRandom(0))
    (made.contains(s"Made($maker)"), claim, result.map(v => broken(v.unwrap)), broken(goodValue), drawn)


  private val ends = Right(List(Broken.Always(NodeId("endsAfterStart"))))

  test("an option: its value, by a match") {
    val tested = Node.claim("Every booking a request may be moved to is itself.")(
      forall((o: Term[Option[Booking]]) => o === o))
    assertEquals(check(shaped(maybeMoved, endFirstMaybe, tested), "maybeMoved", "endFirstMaybe",
      LeanType[Option[Booking]].ty, "tested", Some(bad), Some(good)), (true, Some("(∀ (o : (Option Booking)), " +
      "((match o with | none => True | some b => (Rooms.endsAfterStart b)) → (o = o)))"), ends, Nil, Some(good)))
  }

  test("an either: the side holding a booking, by a match") {
    val tested = Node.claim("Every outcome is itself.")(forall((o: Term[Either[String, Booking]]) => o === o))
    assertEquals(check(shaped(eitherMoved, endFirstEither, tested), "eitherMoved", "endFirstEither",
      LeanType[Either[String, Booking]].ty, "tested", Right(bad), Right(good)), (true,
      Some("(∀ (o : (Except String Booking)), ((match o with | Except.error x => True | " +
        "Except.ok b => (Rooms.endsAfterStart b)) → (o = o)))"), ends, Nil, Right(good)))
  }

  test("a pair: the component holding a booking, by its projection") {
    val tested = Node.claim("Every pair is itself.")(forall((p: Term[(Booking, String)]) => p === p))
    assertEquals(check(shaped(pairMoved, endFirstPair, tested), "pairMoved", "endFirstPair",
      LeanType[(Booking, String)].ty, "tested", (bad, "Oak"), (good, "Oak")), (true,
      Some("(∀ (p : (Booking × String)), ((Rooms.endsAfterStart p.1) → (p = p)))"), ends, Nil, (good, "Oak")))
  }

  test("an enum: each case's field holding a booking, by a match") {
    val tested = Node.claim("Every change is itself.")(forall((c: Term[Change]) => c === c))
    assertEquals(check(shaped(changeMoved, endFirstChange, tested), "changeMoved", "endFirstChange",
      LeanType[Change].ty, "tested", Change.Book(bad), Change.Book(good)), (true,
      Some("(∀ (c : Change), ((match c with | Change.Book b => (Rooms.endsAfterStart b) | " +
        "Change.Cancel room start => True | Change.Clear => True) → (c = c)))"), ends, Nil, Change.Book(good)))
  }
