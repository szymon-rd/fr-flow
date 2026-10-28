package frflow.core

import frflow.core.code.Code
import frflow.core.expr.{Binder, OutsideFact, Prog}
import frflow.core.name.{BoundaryName, DefName, ModelName, OpName, SourceText, SymbolName, VarId}
import frflow.core.spec.Written
import frflow.core.term.{Bound, Program, Stated, Sym, World}
import frflow.core.ty.Ty
import frflow.core.vocab.{BoundarySig, Define, DefineForm, ModelOp, OpSig, StateModel}

/** A store of bookings, its model (an operation adding one), a program `book` calling it, and a claim about its runs,
  * resting on the store behaving as its model and on runs on it being atomic: a valid theory.
  */
object Store:
  val boundary: BoundaryName = BoundaryName("Bookings")
  val model: ModelName = ModelName("stored")
  val book: SymbolName = SymbolName("book")
  private val add = OpName("add")
  private val b = Binder(VarId.level(0), "b", Booking.ty)
  private val held = Binder(VarId.level(1), "held", Ty.ListOf(Booking.ty))

  private def at[A](x: Binder): Stated[A] = Stated([T[_]] => (s: Sym[T]) => s.free[A](x))
  private val added: Stated[List[Booking]] =
    Stated([T[_]] => (s: Sym[T]) => s.cons(s.free[Booking](b), s.free[List[Booking]](held)))

  val sig: BoundarySig = BoundarySig(boundary, "Bookings", "the store of bookings",
    List(OpSig(add, List("b" -> Booking.ty), Ty.Unit)), None)
  val stateModel: StateModel =
    StateModel(model, boundary, Ty.ListOf(Booking.ty), List(ModelOp(add, List(b), Prog.Modify(model, held, added))))
  val program: Define = Define(DefName("bookIfFree"),
    Written.steps(List(b), Prog.Call(boundary, add, List(at[Booking](b)), Ty.Unit), Ty.Unit, SourceText("bookIfFree")),
    DefineForm.Flow)

  /** Every run of `book` ends. */
  val bookRuns: spec.Node = Nodes.claim("bookRuns")(Lang.formula([T[_]] => (l: Lang[T]) =>
    l.forall[Booking]("b", Booking.ty)(x => l.forall[World]("before", Ty.World)(w =>
      l.s.runs(l.call(l.sym[Booking => Program[Unit]]("book", bookTy), x), w, Bound[Unit]("r", Ty.Unit),
        Bound[World]("after", Ty.World))((_, _) => l.truth)))))

  val bookTy: Ty = Ty.FnOf(List(Booking.ty), Ty.FlowOf(Ty.Unit, None))
  val storeModel: spec.Node = Nodes.outside("storeModel")(OutsideFact.BehavesAs(boundary, model))
  val oneAtATime: spec.Node = Nodes.outside("oneAtATime")(OutsideFact.Atomic(boundary))

  val kb: Kb = Kb.of(bookRuns, storeModel, oneAtATime)
    .declaring(_.copy(types = List(Booking.data), defines = List(program), boundaries = List(sig),
      models = List(stateModel)))
    .naming(Nodes.definition("book", bookTy))
    .coding(book -> Code.ProvenFlow(DefName("bookIfFree")))
    .linking(Nodes.assumes("bookRuns", "storeModel"), Nodes.assumes("bookRuns", "oneAtATime"))
