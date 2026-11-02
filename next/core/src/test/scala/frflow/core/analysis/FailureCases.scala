package frflow.core.analysis

import frflow.core.{Booking, Kb, Lang, Store}
import frflow.core.Nodes.*
import frflow.core.expr.{Binder, Prog, Value}
import frflow.core.name.{DefName, NodeId, SourceText, VarId}
import frflow.core.spec.Written
import frflow.core.term.{Bound, Program, Stated, Sym, World}
import frflow.core.ty.Ty
import frflow.core.vocab.{Define, DefineForm, Fails}

/** One theory per problem of a program's error, each the store's valid theory with one change: the store may be down
  * (each call failing with `"down"`), a claim states what a failing run of `book` meets.
  */
object FailureCases:
  /** The store, any call of which may fail with the string `"down"`; `book`'s run read with both outcomes, as a
    * program that can fail must be (`SucceedingOnly`).
    */
  val down: Kb = Store.kb.without("bookRuns").and(bothOutcomes).linking(assumes("bookRuns", "oneAtATime"))
    .declaring(v => v.copy(models = v.models.map(_.copy(fails = Some(Fails(Ty.Str, Value.Str("down")))))))

  /** `∀ b before`, `book(b)`'s runs from `before` that succeed and those that fail. */
  private def bothOutcomes: frflow.core.spec.Node = claim("bookRuns")(Lang.formula([T[_]] => (l: Lang[T]) =>
    l.forall[Booking]("b", Booking.ty)(x => l.forall[World]("before", Ty.World)(w =>
      val run = l.call(l.sym[Booking => Program[Unit]]("book", Store.bookTy), x)
      l.s.and(l.s.runs(run, w, Bound[Unit]("r", Ty.Unit), Bound[World]("after", Ty.World))((_, _) => l.truth),
        l.s.fails(run, w, Bound[Any]("error", Ty.Str), Bound[World]("after", Ty.World))((_, _) => l.truth))))))

  /** `book`'s run read plainly, where it can fail: of the runs that succeed only. */
  val plainly: Kb = Store.kb.declaring(v => v.copy(models = v.models.map(_.copy(fails =
    Some(Fails(Ty.Str, Value.Str("down")))))))

  /** `∀ b before, book(b).from(before).failing { (error: E, after) => true }`. */
  def failing(e: Ty): frflow.core.spec.Node = claim("bookFails")(Lang.formula([T[_]] => (l: Lang[T]) =>
    l.forall[Booking]("b", Booking.ty)(x => l.forall[World]("before", Ty.World)(w =>
      l.s.fails(l.call(l.sym[Booking => Program[Unit]]("book", Store.bookTy), x), w, Bound[Any]("error", e),
        Bound[World]("after", Ty.World))((_, _) => l.truth)))))

  /** The claim of a failing run, resting on one run at a time. */
  def claiming(kb: Kb, e: Ty): Kb = kb.and(failing(e)).linking(assumes("bookFails", "oneAtATime"))

  /** `book`'s program adding the booking, then raising a number: it may fail with the store's string or the number. */
  private val raising: Kb =
    val b = Binder(VarId.level(0), "b", Booking.ty)
    val add = Prog.Call(Store.add, List(Stated([T[_]] => (s: Sym[T]) => s.free[Booking](b))),
      Ty.Unit)
    val steps = Prog.Bind(add, Binder(VarId.step(0), "u", Ty.Unit),
      Prog.Raise(Stated([T[_]] => (s: Sym[T]) => Lang(s).num(1))))
    down.declaring(v => v.copy(defines = List(Define(DefName("bookIfFree"),
      Written.steps(List(b), steps, Ty.Unit, SourceText("bookIfFree")), DefineForm.Flow))))

  /** `book`'s program adding the booking in a transaction inside a transaction. */
  private val nested: Kb =
    val b = Binder(VarId.level(0), "b", Booking.ty)
    val add = Prog.Call(Store.add, List(Stated([T[_]] => (s: Sym[T]) => s.free[Booking](b))),
      Ty.Unit)
    Store.kb.declaring(v => v.copy(defines = List(Define(DefName("bookIfFree"),
      Written.steps(List(b), Prog.Atomic(Prog.Atomic(add)), Ty.Unit, SourceText("bookIfFree")), DefineForm.Flow))))

  /** `book`'s program running a program as a step (`book` itself): no model's operation. */
  private val stepping: Kb =
    val b = Binder(VarId.level(0), "b", Booking.ty)
    val again = Prog.Call(Store.book, List(Stated([T[_]] => (s: Sym[T]) => s.free[Booking](b))), Ty.Unit)
    Store.kb.declaring(v => v.copy(defines = List(Define(DefName("bookIfFree"),
      Written.steps(List(b), again, Ty.Unit, SourceText("bookIfFree")), DefineForm.Flow))))
      .unlinking(assumes("bookRuns", "oneAtATime"))

  /** `book`'s program clearing the store's state in its own steps, not through an operation. */
  private val writing: Kb =
    val b = Binder(VarId.level(0), "b", Booking.ty)
    val held = Binder(VarId.step(0), "held", Ty.ListOf(Booking.ty))
    val cleared = Prog.Modify(Store.model, held, Stated([T[_]] => (s: Sym[T]) => s.nil[Booking](Booking.ty)))
    Store.kb.declaring(v => v.copy(defines = List(Define(DefName("bookIfFree"),
      Written.steps(List(b), cleared, Ty.Unit, SourceText("bookIfFree")), DefineForm.Flow))))
      .unlinking(assumes("bookRuns", "oneAtATime"))

  /** An assumption of `always[Booking]`, which the store's state holds, with nothing saying what it starts in. */
  private val unstarted: Kb = Store.kb.and(assumption("endsAfterStart")(Lang.formula([T[_]] => (l: Lang[T]) =>
    l.s.always(Bound[Booking]("b", Booking.ty))(x => l.s.lt(l.s.field(x, Booking.start), l.s.field(x, Booking.end))))))
    .declaring(v => v.copy(types = List(Booking.data))).linking(assumes("bookRuns", "endsAfterStart"))

  /** `∀ before, before = before`, a claim of worlds equal, where the store may be down. */
  val sameWorld = claim("sameWorld")(Lang.formula([T[_]] => (l: Lang[T]) =>
    l.forall[World]("before", Ty.World)(w => l.s.eq(w, w))))

  /** `∀ p before, p.from(before) { … }`: a run of a program given as a variable, no Definition. */
  private val anyProgram = claim("anyRuns")(Lang.formula([T[_]] => (l: Lang[T]) =>
    l.forall[Program[Unit]]("p", Ty.FlowOf(Ty.Unit, None))(p => l.forall[World]("before", Ty.World)(w =>
      l.s.runs(p, w, Bound[Unit]("r", Ty.Unit), Bound[World]("after", Ty.World))((_, _) => l.truth)))))

  val all: List[ProblemCase] = List(
    ProblemCase(Kb.of(anyProgram), List(Problem.RunOfNoDefinition(NodeId("anyRuns")))),
    ProblemCase(down.and(sameWorld), List(Problem.WorldsEqual(NodeId("sameWorld")))),
    ProblemCase(raising, List(Problem.ErrorsDiffer(DefName("bookIfFree"), List(Lang.big, Ty.Str)))),
    ProblemCase(nested, List(Problem.NestedAtomic(DefName("bookIfFree")))),
    ProblemCase(stepping, List(Problem.StepNotOperation(DefName("bookIfFree"), Store.book))),
    ProblemCase(claiming(down, Lang.big),
      List(Problem.FailingDiffers(NodeId("bookFails"), Store.book, Lang.big, Ty.Str))),
    ProblemCase(claiming(Store.kb, Ty.Str), List(Problem.NeverFails(NodeId("bookFails"), Store.book))),
    ProblemCase(plainly, List(Problem.SucceedingOnly(NodeId("bookRuns"), Store.book))),
    ProblemCase(writing, List(Problem.WritesState(DefName("bookIfFree"), Store.model))),
    ProblemCase(unstarted, List(Problem.NoStart(NodeId("endsAfterStart"), Store.model))))
