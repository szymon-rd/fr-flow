package frflow.proof.lean.lower

import frflow.core.name.{DefName, KbName, ModelName, SymbolName, TypeName}
import frflow.core.ty.{DataType, Ty}
import frflow.proof.lean.ast.*

/** What lowering reads of the FrModel: its name, the open terms each define is over, each model's field of
  * the world and its state's type, what a program's step calls (an operation, by its model's class), each domain
  * type; the programs that may fail, with their error (a run of one is matched on its outcome), whether the world
  * holds faults (a model's operations may fail) and races (a program races two branches), the models' fields of
  * the world, in order, and the model of each operation known only by assumptions (G2).
  */
final case class LowerEnv(kb: KbName, openTerms: DefName => List[LeanName], modelField: ModelName => LeanName,
    operation: SymbolName => LExpr, data: TypeName => Option[DataType], modelState: ModelName => Option[Ty],
    failing: Map[SymbolName, Ty] = Map.empty, faulty: Boolean = false, models: List[LeanName] = Nil,
    twice: Set[DefName] = Set.empty, ruleSide: Boolean = false, racing: Boolean = false,
    assumed: Map[SymbolName, ModelName] = Map.empty, clock: Option[LowerEnv.Clock] = None):
  /** The `def` a call of `d` names: of a define a rule calls, lowered twice (`layout.RuleSide`), the guarded one but
    * where a rule's side is printed (`ruleSide`: a rule, and what it calls).
    */
  def calls(d: DefName): DefName = if twice(d) && !ruleSide then LowerEnv.guarded(d) else d

  /** An open term's type: of an operation known only by assumptions, a constant of its model's state monad
    * (`Account → Search → StateM Tables (List CrmRecord)`), run on its field of the World through `within`; of any
    * other, its type.
    */
  def openType(s: SymbolName, ty: Ty): LExpr =
    assumed.get(s).flatMap(modelState).fold(LowerType.binder(ty))(state => ty match
      case Ty.FnOf(ps, Ty.FlowOf(r, _)) => LowerType.declaration(ps, LowerModels.stateM(LowerType(state), r))
      case Ty.FlowOf(r, _)              => LExpr.Paren(LowerModels.stateM(LowerType(state), r))
      case other                        => LowerType.binder(other))

  /** A program's step calling `op` on its arguments: an operation's method of its model's class
    * (`StoredBookings.Ops.add b`), or, of one known only by assumptions, the open term on its model's state, lifted by
    * the class's `onState` (`DatabaseModel.Ops.onState (fetch u q)`).
    */
  def step(op: SymbolName, args: List[LExpr]): LExpr = assumed.get(op).fold(LExpr.App(operation(op), args))(m =>
    LExpr.App(LowerModels.onState(m), List(LExpr.Paren(LExpr.App(LExpr.Name(Names.ident(op.value)), args)))))

  /** A run of `op` in a statement, of the open term (or what stands for it) `term`: of an operation known only by
    * assumptions, its run on the World (`(DatabaseModel.fetch_run fetch)`), as a program's run is; else `term`.
    */
  def run(op: SymbolName, term: LExpr): LExpr = assumed.get(op).fold(term)(m =>
    LExpr.Paren(LExpr.App(LowerModels.runOf(m, op), List(term))))

  /** The world's own step on the clock, run on the World (`ClockModel.elapse_run`): what an obligation or a
    * statement mentioning it is given for it, as a program is given its run.
    */
  def outside(op: SymbolName): Option[LExpr] =
    clock.filter(_.timed.elapse == op).map(c => LowerModels.runOf(c.model, op))

object LowerEnv:
  /** The clock, where the World has it (owner §47): its model, its steps, and where the schedules let the world move
    * its time (`fun w t => …`, `fun _ _ => True` with none).
    */
  final case class Clock(model: ModelName, timed: frflow.core.vocab.Timed, allows: LExpr)

  /** The second `def` of a define a rule calls, its `forall`s guarded, which statements call. */
  def guarded(d: DefName): DefName = DefName(s"${d.value}_guarded")
