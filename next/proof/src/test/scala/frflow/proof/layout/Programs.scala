package frflow.proof.layout

import frflow.core.{Booking, Kb, Lang}
import frflow.core.Nodes.*
import frflow.core.analysis.{Resolve, Resolved, Validate}
import frflow.core.code.Code
import frflow.core.expr.{Binder, OutsideFact, Prog, Value}
import frflow.core.name.{BoundaryName, DefName, OpName, SourceText, SymbolName, VarId}
import frflow.core.spec.Written
import frflow.core.term.{Bound, Final, Program, Stated, Sym, World}
import frflow.core.ty.Ty
import frflow.core.vocab.{BoundarySig, Define, DefineForm, ModelOp, OpSig, StateModel}

/** Proven code of every shape a rule reads: a define making bookings (`made_reschedule`), a program whose result is
  * one (`made_fetch`, and of one with no inputs, `made_latest`), a store's operation giving one on its model
  * (`made_sample`), a pair of steps at once
  * (`commute_0` of `pairUp`) and a traverse at once (`commute_0` of
  * `eachDoubled`), and a program raising, handling, collecting and accumulating (`careful`, its define only).
  */
object Programs:
  private val big = Lang.big
  private def at(i: Int, hint: String, ty: Ty) = Binder(VarId.level(i), hint, ty)
  private def step(i: Int, hint: String, ty: Ty) = Binder(VarId.step(i), hint, ty)
  private def term[A](f: [T[_]] => Sym[T] => T[A]): Stated[A] = Stated([T[_]] => (s: Sym[T]) => f(s))
  private def v[A](x: Binder): Stated[A] = term([T[_]] => (s: Sym[T]) => s.free[A](x))
  private def plus(a: Binder, b: Binder): Stated[BigInt] = term([T[_]] => (s: Sym[T]) => s.add(s.free(a), s.free(b)))
  private def flow(name: String, inputs: List[Binder], p: Prog[Stated[?]], result: Ty): List[Define] = List(
    Define(DefName(name), Written.steps(inputs, p, result, SourceText(name)), DefineForm.Flow),
    Define(DefName(s"${name}_run"), Written.steps(inputs, p, result, SourceText(name)),
      DefineForm.RunOf(DefName(name))))

  private val b = at(0, "b", Booking.ty)
  private val n = at(0, "n", big)
  private val xs = at(0, "xs", Ty.ListOf(big))
  private val endsRule = Define(DefName("endsAfterStart"), Written.lambda(List(b), [T[_]] => (s: Sym[T]) =>
    s.lt(s.field(s.free[Booking](b), Booking.start), s.field(s.free[Booking](b), Booking.end)),
    SourceText("endsAfterStart")), DefineForm.Function)
  private val later = Define(DefName("later"), Written.lambda(List(b), [T[_]] => (s: Sym[T]) =>
    s.copy(s.free[Booking](b), Booking.start, s.field(s.free[Booking](b), Booking.start)), SourceText("later")),
    DefineForm.Function)
  private val made: Stated[Booking] = term([T[_]] => (s: Sym[T]) =>
    s.app(s.app(s.app(s.construct(Booking.make), Lang(s).str("")), Lang(s).num(0)), Lang(s).num(1)))
  private val (a, c) = (step(0, "a", big), step(1, "c", big))
  private val both = Prog.Par(Prog.Pure(v[BigInt](n)), a,
    Prog.Pure(term([T[_]] => (s: Sym[T]) => s.add(s.free[BigInt](n), Lang(s).num(1)))), c)
  private val x = step(0, "x", big)
  private val each = Prog.ParEach(v[List[BigInt]](xs), x, Prog.Pure(plus(x, x)), None)
  private val (e, r0, y, ys, acc, z) = (step(0, "e", Ty.Str), step(1, "r", big), step(2, "y", big),
    step(3, "ys", Ty.ListOf(big)), step(4, "acc", big), step(5, "z", big))
  private val careful = Prog.Bind(Prog.Catch(Prog.Raise(term([T[_]] => (s: Sym[T]) => Lang(s).str("no"))), Ty.Str, e,
    Prog.Pure(v[BigInt](n))), r0, Prog.Bind(Prog.Collect(term([T[_]] => (s: Sym[T]) =>
      s.lit(List(BigInt(1), BigInt(2)), Value.Many(List(Value.Num(1), Value.Num(2))), Ty.ListOf(big))), y,
      Prog.Pure(plus(y, r0))), ys, Prog.Accumulate(v[List[BigInt]](ys), term([T[_]] => (s: Sym[T]) =>
      Lang(s).num(0)), acc, z, Prog.Pure(plus(acc, z)))))

  private def fn(in: Ty, out: Ty) = Ty.FnOf(List(in), out)
  private def runs[I, R](name: String, in: Ty, out: Ty): Final[Boolean] = Lang.formula([T[_]] => (l: Lang[T]) =>
    l.forall[I]("i", in)(i => l.forall[World]("before", Ty.World)(w => l.s.runs(
      l.call(l.sym[I => Program[R]](name, fn(in, Ty.FlowOf(out, None))), i), w, Bound[R]("r", out),
      Bound[World]("after", Ty.World))((_, _) => l.truth))))

  val endsAfterStart: frflow.core.spec.Node = claim("endsAfterStart")(Lang.formula([T[_]] => (l: Lang[T]) =>
    l.s.always(Bound[Booking]("b", Booking.ty))(x => l.s.lt(l.s.field(x, Booking.start), l.s.field(x, Booking.end)))))
  private val laterSame = claim("laterSame")(Lang.formula([T[_]] => (l: Lang[T]) =>
    l.forall[Booking]("b", Booking.ty)(x => l.s.eq(l.s.field(l.call(l.sym[Booking => Booking]("reschedule",
      fn(Booking.ty, Booking.ty)), x), Booking.start), l.s.field(x, Booking.start)))))

  /** A shelf of bookings whose one operation gives a booking: `made_sample`, on its model. */
  private val shelf = frflow.core.name.ModelName("shelved")
  private val shelfSig = BoundarySig(BoundaryName("Shelf"), "Shelf", "a shelf of bookings",
    List(OpSig(OpName("sample"), Nil, Booking.ty)), None)
  private val shelfModel = StateModel(shelf, shelfSig.name, Ty.ListOf(Booking.ty),
    List(ModelOp(OpName("sample"), Nil, Prog.Pure(made))))
  private val held = at(0, "held", Ty.ListOf(Booking.ty))
  private val emptyRule = Define(DefName("shelfEmpty"), Written.lambda(List(held), [T[_]] => (s: Sym[T]) =>
    s.eq(s.free[List[Booking]](held), s.nil[Booking](Booking.ty)), SourceText("shelfEmpty")), DefineForm.Function)
  private val shelfFacts = List(outside("shelfModel")(OutsideFact.BehavesAs(shelfSig.name, shelf)),
    outside("shelfOneRun")(OutsideFact.OneRunAtATime(shelf)),
    outside("shelfEmpty")(OutsideFact.Initially(shelf, DefName("shelfEmpty"))),
    outside("shelfUntouched")(OutsideFact.WrittenOnlyBy(shelf, Nil)))

  val kb: Kb = Kb.of(endsAfterStart, laterSame, claim("fetchRuns")(runs[BigInt, Booking]("fetch", big, Booking.ty)),
      claim("pairRuns")(runs[BigInt, (BigInt, BigInt)]("pairUp", big, Ty.TupleOf(List(big, big)))),
      claim("eachRuns")(runs[List[BigInt], List[BigInt]]("eachDoubled", Ty.ListOf(big), Ty.ListOf(big))),
      claim("latestRuns")(Fixture.runsAlone[Booking]("latest", Booking.ty)),
      assumption("fromOutside")(Lang.formula([T[_]] => (l: Lang[T]) =>
      l.s.always(Bound[Booking]("b", Booking.ty))(x =>
        l.s.lt(l.s.field(x, Booking.start), l.s.field(x, Booking.end))))))
    .and(shelfFacts*)
    .declaring(_.copy(types = List(Booking.data), boundaries = List(shelfSig), models = List(shelfModel),
      defines = List(endsRule, later, emptyRule) ++
      flow("fetchOne", List(n), Prog.Pure(made), Booking.ty) ++ flow("newest", Nil, Prog.Pure(made), Booking.ty) ++
      flow("both", List(n), both, Ty.TupleOf(List(big, big))) ++
      flow("doubled", List(xs), each, Ty.ListOf(big)) ++
      flow("careful", List(n), careful, big).take(1)))
    .naming(definition("reschedule", fn(Booking.ty, Booking.ty)),
      definition("fetch", fn(big, Ty.FlowOf(Booking.ty, None))),
      definition("pairUp", fn(big, Ty.FlowOf(Ty.TupleOf(List(big, big)), None))),
      definition("eachDoubled", fn(Ty.ListOf(big), Ty.FlowOf(Ty.ListOf(big), None))),
      definition("latest", Ty.FlowOf(Booking.ty, None)))
    .coding(SymbolName("reschedule") -> Code.Proven(DefName("later")),
      SymbolName("fetch") -> Code.ProvenFlow(DefName("fetchOne")),
      SymbolName("pairUp") -> Code.ProvenFlow(DefName("both")),
      SymbolName("eachDoubled") -> Code.ProvenFlow(DefName("doubled")),
      SymbolName("latest") -> Code.ProvenFlow(DefName("newest")))
    .linking(("fromOutside" :: shelfFacts.map(_.id.value)).map(assumes("endsAfterStart", _))*)
    .linking(List("laterSame", "fetchRuns", "pairRuns", "eachRuns", "latestRuns").map(assumes(_, "fromOutside"))*)

  lazy val resolved: Resolved = Resolve(Validate(kb.elaborated).fold(ps => throw IllegalStateException(ps.toString),
    identity))
