package frflow.core.analysis

import frflow.core.{Booking, Kb, Lang, Store}
import frflow.core.Nodes.*
import frflow.core.code.Code
import frflow.core.expr.{Binder, OutsideFact}
import frflow.core.name.{DefName, SourceText, SymbolName, VarId}
import frflow.core.spec.Written
import frflow.core.term.{Bound, Final, Program, Sym, World}
import frflow.core.ty.Ty
import frflow.core.vocab.{Define, DefineForm, OpSig}

/** One theory per problem of an operation known only by assumptions (G2): the store's valid theory with `peek`, an
  * operation of its model given no steps, and an assumption about its runs.
  */
object AssumedCases:
  val peek: SymbolName = SymbolName("peek")
  private val peekTy = Ty.FlowOf(Ty.ListOf(Booking.ty), None)

  /** `∀ before, peek.from(before) { (r, after) => r = r }`: of its result, not of the world it leaves. */
  private val peekGives = assumption("peekGives")(Lang.formula([T[_]] => (l: Lang[T]) =>
    l.forall[World]("before", Ty.World)(w => l.s.runs(l.sym[Program[List[Booking]]]("peek", peekTy), w,
      Bound[List[Booking]]("r", Ty.ListOf(Booking.ty)), Bound[World]("after", Ty.World))((r, _) => l.s.eq(r, r)))))

  /** The store with `peek`, known by `peekGives`. */
  def peeking(kb: Kb): Kb = kb.and(peekGives)
    .declaring(v => v.copy(models = v.models.map(_.copy(assumed = List(OpSig(peek, Nil, Ty.ListOf(Booking.ty)))))))
    .naming(definition("peek", peekTy)).coding(peek -> Code.Modelled(Store.model))

  /** What the store starts in: no booking. */
  private val startsEmpty: Define =
    val held = Binder(VarId.level(0), "held", Ty.ListOf(Booking.ty))
    val body: Final[Boolean] = [T[_]] => (s: Sym[T]) =>
      s.eq(s.free[List[Booking]](held), s.nil[Booking](Booking.ty))
    Define(DefName("startsEmpty"), Written.lambda(List(held), body, SourceText("startsEmpty")), DefineForm.Function)

  private def same(id: String, assumed: Boolean) =
    val f = Lang.formula([T[_]] => (l: Lang[T]) => l.s.always(Bound[Booking]("b", Booking.ty))(b => l.s.eq(b, b)))
    if assumed then assumption(id)(f) else claim(id)(f)

  /** A claim of `always[Booking]`, which the store's state holds, resting on what the store starts in and on what
    * the bookings from outside meet.
    */
  private val kept: Kb = Store.kb.and(same("kept", false), same("fromForm", true),
    outside("starts")(OutsideFact.Initially(Store.model, DefName("startsEmpty"))))
    .declaring(v => v.copy(types = List(Booking.data), defines = v.defines :+ startsEmpty))
    .linking(assumes("kept", "onlyCode"), assumes("kept", "oneAtATime"), assumes("kept", "starts"),
      assumes("kept", "fromForm"), assumes("bookRuns", "fromForm"))

  /** `∀ before, peek.from(before) { (_, after) => after = before }`: what its runs leave. */
  private val peekKeeps = assumption("peekKeeps")(Lang.formula([T[_]] => (l: Lang[T]) =>
    l.forall[World]("before", Ty.World)(w => l.s.runs(l.sym[Program[List[Booking]]]("peek", peekTy), w,
      Bound[List[Booking]]("r", Ty.ListOf(Booking.ty)), Bound[World]("after", Ty.World))((_, a) => l.s.eq(a, w)))))

  /** The rule's theory with `peek` said to leave the world as it was: valid. */
  val saidWhatItLeaves: Kb = peeking(kept).and(peekKeeps)
  /** `peek` with nothing assumed of it: undefined. */
  val unsaid: Kb = peeking(kept).without("peekGives")

  val all: List[ProblemCase] = List(
    ProblemCase(peeking(kept), List(Problem.LeavesUnsaid(peek, Store.model))),
    ProblemCase(peeking(FailureCases.down), List(Problem.AssumedFailing(peek, Store.model))))
