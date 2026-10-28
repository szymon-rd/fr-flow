package frflow.proof.layout

import frflow.core.{Booking, Lang}
import frflow.core.Nodes.*
import frflow.core.expr.{Binder, OutsideFact, Prog}
import frflow.core.name.{BoundaryName, DefName, ModelName, SourceText, VarId}
import frflow.core.spec.{Node, Written}
import frflow.core.term.{Bound, Final, Program, Selector, Stated, Sym, World}
import frflow.core.ty.Ty
import frflow.core.vocab.{Define, DefineForm}

/** What the test theories of proven code are written with: variables, terms, programs and their runs, and what
  * always holds of a booking (its rule, the claim, and the assumption of it on what comes from outside).
  */
object Fixture:
  def at(i: Int, hint: String, ty: Ty): Binder = Binder(VarId.level(i), hint, ty)
  def step(i: Int, hint: String, ty: Ty): Binder = Binder(VarId.step(i), hint, ty)
  def term[A](f: [T[_]] => Sym[T] => T[A]): Stated[A] = Stated([T[_]] => (s: Sym[T]) => f(s))
  def v[A](x: Binder): Stated[A] = term([T[_]] => (s: Sym[T]) => s.free[A](x))
  def fn(in: Ty, out: Ty): Ty = Ty.FnOf(List(in), out)
  /** A booking's room (core's fixtures read its times only). */
  val room: Selector[Booking, String] = Selector("room", 0, Booking.name, Ty.Str, _.room, (b, r) => b.copy(room = r))

  /** A program's define and its run on the models. */
  def flow(name: String, inputs: List[Binder], p: Prog[Stated[?]], result: Ty): List[Define] = List(
    Define(DefName(name), Written.steps(inputs, p, result, SourceText(name)), DefineForm.Flow),
    Define(DefName(s"${name}_run"), Written.steps(inputs, p, result, SourceText(name)),
      DefineForm.RunOf(DefName(name))))

  /** `(Booking.mk room start end)`. */
  def booking[T[_]](s: Sym[T], room: T[String], start: T[BigInt], end: T[BigInt]): T[Booking] =
    s.app(s.app(s.app(s.construct(Booking.make), room), start), end)

  private val b = at(0, "b", Booking.ty)
  /** `b.start < b.end`, a define named as the claim of it. */
  val endsRule: Define = rule("endsAfterStart")
  /** The same rule, a define named as another statement of it (an assumption of always has its rule too). */
  def rule(name: String): Define = Define(DefName(name), Written.lambda(List(b), [T[_]] => (s: Sym[T]) =>
    s.lt(s.field(s.free[Booking](b), Booking.start), s.field(s.free[Booking](b), Booking.end)),
    SourceText(name)), DefineForm.Function)

  private val ends: Final[Boolean] = Lang.formula([T[_]] => (l: Lang[T]) =>
    l.s.always(Bound[Booking]("b", Booking.ty))(x => l.s.lt(l.s.field(x, Booking.start), l.s.field(x, Booking.end))))
  val endsAfterStart: Node = claim("endsAfterStart")(ends)
  /** What the outside sends meets the same rule (owner §21). */
  def fromOutside(id: String): Node = assumption(id)(ends)

  /** A store's three facts: behaves as its model (nothing outside the code changing it), runs on it atomic, starts
    * empty (`emptyRule`). The programs changing it are derived.
    */
  def storeFacts(boundary: BoundaryName, m: ModelName): List[Node] = List(
    outside("shelfModel")(OutsideFact.BehavesAs(boundary, m)), outside("shelfOneRun")(OutsideFact.Atomic(boundary)),
    outside("shelfEmpty")(OutsideFact.Initially(m, DefName("shelfEmpty"))))

  private val held = at(0, "held", Ty.ListOf(Booking.ty))
  val emptyRule: Define = Define(DefName("shelfEmpty"), Written.lambda(List(held), [T[_]] => (s: Sym[T]) =>
    s.eq(s.free[List[Booking]](held), s.nil[Booking](Booking.ty)), SourceText("shelfEmpty")), DefineForm.Function)

  /** Every run of the program `name` from every world, on every input of type `in`, ends. */
  def runs[I, R](name: String, in: Ty, out: Ty): Final[Boolean] = Lang.formula([T[_]] => (l: Lang[T]) =>
    l.forall[I]("i", in)(i => l.forall[World]("before", Ty.World)(w => l.s.runs(
      l.call(l.sym[I => Program[R]](name, fn(in, Ty.FlowOf(out, None))), i), w, Bound[R]("r", out),
      Bound[World]("after", Ty.World))((_, _) => l.truth))))

  /** The same of a program with no inputs. */
  def runsAlone[R](name: String, out: Ty): Final[Boolean] = Lang.formula([T[_]] => (l: Lang[T]) =>
    l.forall[World]("before", Ty.World)(w => l.s.runs(l.sym[Program[R]](name, Ty.FlowOf(out, None)), w,
      Bound[R]("r", out), Bound[World]("after", Ty.World))((_, _) => l.truth)))
