package frflow.core

import frflow.core.code.Code
import frflow.core.expr.{Binder, OutsideFact, Prog}
import frflow.core.name.{DefName, ModelName, SourceText, SymbolName, VarId}
import frflow.core.spec.Written
import frflow.core.term.{Bound, Program, Stated, Sym, World}
import frflow.core.ty.Ty
import frflow.core.vocab.{Define, DefineForm, ModelOp, StateModel}

/** A store of bookings: its operation `add`, a Definition its model gives the meaning (a booking added), a program
  * `book` calling it, and a claim about its runs, resting on runs on the store being atomic; and the assumption that
  * nothing outside the code changes it. A valid theory.
  */
object Store:
  val model: ModelName = ModelName("stored")
  val book: SymbolName = SymbolName("book")
  val add: SymbolName = SymbolName("add")
  private val b = Binder(VarId.level(0), "b", Booking.ty)
  private val held = Binder(VarId.level(1), "held", Ty.ListOf(Booking.ty))

  private def at[A](x: Binder): Stated[A] = Stated([T[_]] => (s: Sym[T]) => s.free[A](x))
  private val added: Stated[List[Booking]] =
    Stated([T[_]] => (s: Sym[T]) => s.cons(s.free[Booking](b), s.free[List[Booking]](held)))

  val stateModel: StateModel = StateModel(model, "the store of bookings", Ty.ListOf(Booking.ty),
    List(ModelOp(add, List(b), Ty.Unit, Prog.Modify(model, held, added))), None)
  val program: Define = Define(DefName("bookIfFree"),
    Written.steps(List(b), Prog.Call(add, List(at[Booking](b)), Ty.Unit), Ty.Unit, SourceText("bookIfFree")),
    DefineForm.Flow)

  val bookTy: Ty = Ty.FnOf(List(Booking.ty), Ty.FlowOf(Ty.Unit, None))

  /** Every run of `book` ends. */
  val bookRuns: spec.Node = Nodes.claim("bookRuns")(Lang.formula([T[_]] => (l: Lang[T]) =>
    l.forall[Booking]("b", Booking.ty)(x => l.forall[World]("before", Ty.World)(w =>
      l.s.runs(l.call(l.sym[Booking => Program[Unit]]("book", bookTy), x), w, Bound[Unit]("r", Ty.Unit),
        Bound[World]("after", Ty.World))((_, _) => l.truth)))))

  val onlyCode: spec.Node = Nodes.outside("onlyCode")(OutsideFact.OnlyCodeChanges(model))
  val oneAtATime: spec.Node = Nodes.outside("oneAtATime")(OutsideFact.Atomic(model))

  val kb: Kb = Kb.of(bookRuns, onlyCode, oneAtATime)
    .declaring(_.copy(types = List(Booking.data), defines = List(program)))
    .modelling(stateModel)
    .naming(Nodes.definition("book", bookTy))
    .coding(book -> Code.ProvenFlow(DefName("bookIfFree")))
    .linking(Nodes.assumes("bookRuns", "oneAtATime"))
