package frflow.core.analysis

import frflow.core.{Booking, Kb, Lang, Store}
import frflow.core.Nodes.*
import frflow.core.expr.{Binder, Prog, Value}
import frflow.core.name.{DefName, NodeId, OpName, SourceText, VarId}
import frflow.core.spec.Written
import frflow.core.term.{Bound, Program, Stated, Sym, World}
import frflow.core.ty.Ty
import frflow.core.vocab.{Define, DefineForm, Fails}

/** One theory per problem of a program's error, each the store's valid theory with one change: the store may be down
  * (each call failing with `"down"`), a claim states what a failing run of `book` meets.
  */
object FailureCases:
  /** The store, any call of which may fail with the string `"down"`. */
  val down: Kb = Store.kb.declaring(v => v.copy(boundaries = v.boundaries.map(_.copy(fails =
    Some(Fails(Ty.Str, Value.Str("down")))))))

  /** `∀ b before, book(b).from(before).failing { (error: E, after) => true }`. */
  def failing(e: Ty): frflow.core.spec.Node = claim("bookFails")(Lang.formula([T[_]] => (l: Lang[T]) =>
    l.forall[Booking]("b", Booking.ty)(x => l.forall[World]("before", Ty.World)(w =>
      l.s.fails(l.call(l.sym[Booking => Program[Unit]]("book", Store.bookTy), x), w, Bound[Any]("error", e),
        Bound[World]("after", Ty.World))((_, _) => l.truth)))))

  /** The claim of a failing run, resting on the store's model and on one run at a time. */
  def claiming(kb: Kb, e: Ty): Kb = kb.and(failing(e))
    .linking(assumes("bookFails", "storeModel"), assumes("bookFails", "oneAtATime"))

  /** `book`'s program adding the booking, then raising a number: it may fail with the store's string or the number. */
  private val raising: Kb =
    val b = Binder(VarId.level(0), "b", Booking.ty)
    val add = Prog.Call(Store.boundary, OpName("add"), List(Stated([T[_]] => (s: Sym[T]) => s.free[Booking](b))),
      Ty.Unit)
    val steps = Prog.Bind(add, Binder(VarId.step(0), "u", Ty.Unit),
      Prog.Raise(Stated([T[_]] => (s: Sym[T]) => Lang(s).num(1))))
    down.declaring(v => v.copy(defines = List(Define(DefName("bookIfFree"),
      Written.steps(List(b), steps, Ty.Unit, SourceText("bookIfFree")), DefineForm.Flow))))

  val all: List[ProblemCase] = List(
    ProblemCase(raising, List(Problem.ErrorsDiffer(DefName("bookIfFree"), List(Ty.Str, Lang.big)))),
    ProblemCase(claiming(down, Lang.big),
      List(Problem.FailingDiffers(NodeId("bookFails"), Store.book, Lang.big, Ty.Str))),
    ProblemCase(claiming(Store.kb, Ty.Str), List(Problem.NeverFails(NodeId("bookFails"), Store.book))))
