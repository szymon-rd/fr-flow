package frflow.proof.lean.lower

import cats.syntax.all.*
import frflow.core.expr.Binder
import frflow.core.name.{DefName, LeanNames, ModelName, SymbolName, VarId}
import frflow.core.ty.Ty
import frflow.core.vocab.{Define, OpSig, StateModel}
import frflow.proof.lean.ast.*

/** The models as Lean (`Models.lean`): each model's class of its operations (`Stored.Ops`, the operations named as
  * their Definitions); each operation's meaning on the model's state, a `do` block of the steps its `means` records
  * (`LowerProg`); the `World` the models are parts of, with the faults the failing models' calls take; each class's
  * instance on `StateM World` and its lemmas, and on `ExceptT E (StateM World)` for each error `E` a program fails
  * with (`LowerFaults`). And a program's run on the models (`f_run`), what `impl` is asked of. A model with operations
  * known only by assumptions (G2) has `onState` in its class, a step on its state run on its field of the World, and
  * each such operation's run on the World (`fetch_run`), what a statement reads.
  */
final class LowerModels(env: LowerEnv, naming: Naming):
  import Atoms.{call, const, name}
  private val faults = LowerFaults(env, naming)

  def decls(models: List[StateModel], errors: List[Ty]): List[Decl] =
    models.map(classOf) ++ models.map(model) ++ List(world(models)) ++ models.map(instance) ++
      models.flatMap(lemmas) ++ models.flatMap(m => m.assumed.map(assumedRun(m, _))) ++ faults.decls(models, errors) ++
      (if env.racing then LowerFaults.racesDecls else Nil) ++ LowerFaults.clockDecls(env, fields(models))

  /** `@[frflow_defs] def Model.op_run (op : A → StateM S R) : A → World → (R × World) := fun a w => FrFlow.runOn
    * (FrFlow.within … (op a)) w`: an operation known only by assumptions run on its field of the World.
    */
  private def assumedRun(m: StateModel, o: OpSig): Decl =
    val (op, ps, w) = (Names.ident(o.name.value), LowerModels.params(naming, o), Names.builtin("w"))
    val called = if ps.isEmpty then LExpr.Name(op) else LExpr.App(LExpr.Name(op), ps.map(LExpr.Name(_)))
    val flow = Ty.FlowOf(o.result, None)
    val opTy = env.openType(o.name, if o.params.isEmpty then flow else Ty.FnOf(o.params.map(_._2), flow))
    Decl.Def(List(Attr.FrflowDefs), Names.builtin(s"${LowerModels.space(m).text}.${LowerModels.runName(o.name)}"),
      List(LBinder.Explicit(op, opTy)), LowerType.declaration(o.params.map(_._2) :+ Ty.World, pairWithWorld(o.result)),
      LExpr.Fun(ps.zip(o.params).map((n, p) => typed(n, p._2)) :+ LBinder.Explicit(w, name("World")),
        call(const("FrFlow.runOn"), List(LExpr.Paren(LowerModels.within(env, m.name, called)), LExpr.Name(w)))))

  /** `def f_run (open terms) : A → World → (R × World) := fun a w => (FrFlow.runOn ((K.f open terms) a) w)`; of a
    * program that may fail with `E`, `… → World → ((Except E R) × World) := fun a w => (FrFlow.runOnE (ε := E) … w)`.
    */
  def run(d: Define, flow: DefName, opens: List[(SymbolName, Ty)]): Decl =
    val inputs = d.lambda.params
    val (result, error) = (Ty.yields(d.lambda.result), Ty.errorOf(d.lambda.result))
    val (n, names) = inputs.traverse(Naming.bind).run(naming).value
    val w = Naming.helper("w", Set.empty).runA(n).value
    val ran = names.foldLeft(Atoms.define(env, flow))((f, a) => call(f, List(LExpr.Name(a))))
    val runOn = error.fold(const("FrFlow.runOn"))(e => LExpr.Named(const("FrFlow.runOnE"), Names.builtin("ε"),
      LowerType(e)))
    val outcome = error.fold(result)(Ty.EitherOf(_, result))
    Decl.Def(List(Attr.FrflowDefs), Names.ident(d.name.value),
      opens.map((s, t) => LBinder.Explicit(Names.ident(s.value), env.openType(s, t))),
      LowerType.declaration(inputs.map(_.ty) :+ Ty.World, pairWithWorld(outcome)),
      LExpr.Fun(inputs.zip(names).map((x, a) => typed(a, x.ty)) :+ LBinder.Explicit(w, name("World")),
        call(runOn, List(ran, LExpr.Name(w)))))

  /** `namespace Stored def inRoom_of (room : String) (s : (List Booking)) : RoomBookings := Id.run ((Stored.inRoom
    * room).run' s)`: an operation's result on its model's state, which `made_<op>` is stated of.
    */
  def resultOf(m: StateModel, o: OpSig): Decl =
    val inputs = o.params.zipWithIndex.map { case ((p, t), i) => Binder(VarId.level(i), p, t) }
    val (n, names) = inputs.traverse(Naming.bind).run(naming).value
    val s = Naming.helper("s", Set.empty).runA(n).value // apart from the parameters' names
    val op = LExpr.App(LExpr.Const(List(LowerModels.space(m), Names.ident(o.name.value))), names.map(LExpr.Name(_)))
    val ran = LExpr.App(LExpr.Dot(LExpr.Paren(op), "run'"), List(LExpr.Name(s)))
    Decl.Namespace(List(LowerModels.space(m)), List(Decl.Def(List(Attr.FrflowDefs),
      Names.ident(LeanNames.ofOp(o.name.value)), inputs.zip(names).map((x, a) => typed(a, x.ty)) :+ typed(s, m.state),
      LowerType(o.result), LExpr.App(const("Id.run"), List(LExpr.Paren(ran))))))

  private def classOf(m: StateModel): Decl =
    val monad = Naming.helper("m", Set.empty).runA(naming).value
    Decl.Documented(s"The operations on ${m.name.value}: ${m.means}", Decl.Class(LowerModels.className(m),
      List(LBinder.Explicit(monad, LExpr.Infix(LOp.Arrow, name("Type"), name("Type")))),
      m.sigs.map(o => Names.ident(o.name.value) ->
        LowerType.declaration(o.params.map(_._2), LExpr.App(LExpr.Name(monad), List(LowerType(o.result))))) ++
        Option.when(m.assumed.nonEmpty)(LowerModels.OnState -> onStateType(m, LExpr.Name(monad)))))

  /** `∀ {α : Type}, StateM S α → m α`: a step on the model's state, in the monad. */
  private def onStateType(m: StateModel, monad: LExpr): LExpr =
    val a = Names.builtin("α")
    LExpr.Forall(List(LBinder.Implicit(a, name("Type"))), LExpr.Infix(LOp.Arrow,
      LExpr.App(name("StateM"), List(LowerType(m.state), LExpr.Name(a))), LExpr.App(monad, List(LExpr.Name(a)))))

  /** `namespace Stored`: each operation's meaning, a `do` block on the model's state. */
  def model(m: StateModel): Decl =
    Decl.Namespace(List(LowerModels.space(m)), m.ops.map { op =>
      val (bs, lines) = (op.params.traverse(x => Naming.bind(x).map(typed(_, x.ty))),
        LowerProg(env, op.params.size).block(op.steps)).tupled.runA(naming).value
      val body = if bs.isEmpty then LExpr.Do(lines, 4) else LExpr.Fun(bs, LExpr.Do(lines, 4))
      Decl.Def(List(Attr.FrflowDefs), Names.ident(op.op.value), Nil,
        LowerType.declaration(op.params.map(_.ty), LowerModels.stateM(LowerType(m.state), op.result)), body)
    })

  /** The World's fields, in order. */
  private def fields(models: List[StateModel]): List[LeanName] = world(models) match
    case Decl.Documented(_, Decl.Structure(_, fs)) => fs.map(_._1)
    case _                                         => Nil

  /** The models' states, the faults when a model's operations may fail (`true`: that call fails, in order), the
    * races' winners when a program races (`true`: the left wins, in order), and the time the world lets pass at each
    * of the clock's steps when the World has the clock (owner §47).
    */
  private def world(models: List[StateModel]): Decl =
    val failing = Option.when(models.exists(_.fails.nonEmpty))(LowerFaults.field -> LowerFaults.listOfBool)
    val racing = Option.when(env.racing)(LowerFaults.racesField -> LowerFaults.listOfBool)
    val ticking = env.clock.map(_ => LowerFaults.ticksField -> LowerFaults.listOfNat)
    Decl.Documented("The models' states: what proven flows run on.", Decl.Structure(Names.builtin("World"),
      models.map(m => env.modelField(m.name) -> LowerType(m.state)) ++ failing ++ racing ++ ticking))

  private def instance(m: StateModel): Decl =
    Decl.Instance(LExpr.App(LExpr.Name(LowerModels.className(m)),
      List(LExpr.Paren(LExpr.App(name("StateM"), List(name("World")))))),
      m.sigs.map { o =>
        val ps = LowerModels.params(naming, o)
        InstanceField(Names.ident(o.name.value), ps, LowerModels.onWorld(env, m, o, ps))
      } ++ Option.when(m.assumed.nonEmpty)(InstanceField(LowerModels.OnState, List(Names.builtin("x")),
        LowerModels.within(env, m.name, LExpr.Name(Names.builtin("x"))))))

  private def lemmas(m: StateModel): List[Decl] =
    m.sigs.map(o => LowerModels.lemma((m, o), "_onWorld", LowerModels.stateM(name("World"), o.result), naming)(
      LowerModels.onWorld(env, m, o, _))) ++ Option.when(m.assumed.nonEmpty)(onStateLemma(m))

  /** `@[frflow_defs] theorem Model.Ops.onState_onWorld {α : Type} (x : StateM S α) : ((Model.Ops.onState x) :
    * StateM World α) = FrFlow.within … x := rfl`.
    */
  private def onStateLemma(m: StateModel): Decl =
    val (a, x) = (Names.builtin("α"), Names.builtin("x"))
    val own = LExpr.App(LowerModels.onState(m.name), List(LExpr.Name(x)))
    Decl.Theorem(List(Attr.FrflowDefs), Names.builtin(s"${LowerModels.className(m).text}.onState_onWorld"),
      List(LBinder.Implicit(a, name("Type")), LBinder.Explicit(x, LExpr.App(name("StateM"),
        List(LowerType(m.state), LExpr.Name(a))))), LExpr.Infix(LOp.Eq, LExpr.Typed(LExpr.Paren(own),
        LExpr.App(name("StateM"), List(name("World"), LExpr.Name(a)))),
        LowerModels.within(env, m.name, LExpr.Name(x))), Proof.Rfl, Break.NextLine)

  private def pairWithWorld(r: Ty): LExpr = LExpr.Paren(LExpr.Infix(LOp.Times, LowerType(r), name("World")))
  private def typed(n: LeanName, t: Ty): LBinder = LBinder.Explicit(n, LowerType.binder(t))

object LowerModels:
  import Atoms.{const, name}

  /** `FrFlow.within (fun w => w.f) (fun w s => { w with f := s }) (Model.op args)`: the model's operation on its
    * part of the world.
    */
  def onWorld(env: LowerEnv, m: StateModel, o: OpSig, names: List[LeanName]): LExpr = LowerFaults.timed(env, m.name,
    o.name, within(env, m.name, LExpr.App(LExpr.Const(List(space(m), Names.ident(o.name.value))),
      names.map(LExpr.Name(_)))))

  /** `FrFlow.within (fun w => w.f) (fun w s => { w with f := s }) (step)`: a step on a model's state run on its part
    * of the world.
    */
  def within(env: LowerEnv, m: ModelName, step: LExpr): LExpr =
    val (w, s, field) = (Names.builtin("w"), Names.builtin("s"), env.modelField(m))
    val get = LExpr.Fun(List(LBinder.Bare(w)), LExpr.Dot(LExpr.Name(w), field.text))
    val update = LExpr.Update(LExpr.Name(w), List(field -> LExpr.Name(s)))
    val set = LExpr.Fun(List(LBinder.Bare(w), LBinder.Bare(s)), update)
    LExpr.App(const("FrFlow.within"), List(LExpr.Paren(get), LExpr.Paren(set), LExpr.Paren(step)))

  /** The class method lifting a step on the model's state (`DatabaseModel.Ops.onState`), what a program's call of an
    * operation known only by assumptions is (G2).
    */
  def onState(m: ModelName): LExpr = LExpr.Const(List(Names.builtin(s"${space(m).text}.Ops"), OnState))
  val OnState: LeanName = Names.builtin("onState")
  /** An operation known only by assumptions, run on the World (`DatabaseModel.fetch_run`). */
  def runOf(m: ModelName, op: SymbolName): LExpr = LExpr.Const(List(space(m), Names.builtin(runName(op))))
  def runName(op: SymbolName): String = LeanNames.ident(op.value + "_run")

  /** `@[frflow_defs] theorem Class.op_<suffix> (params) : ((Class.op args) : monad) = value := rfl`. */
  def lemma(op: (StateModel, OpSig), suffix: String, monad: LExpr, naming: Naming)(value: List[LeanName] => LExpr)
      : Decl =
    val (m, o) = op
    val names = params(naming, o)
    val own = LExpr.App(LExpr.Const(List(className(m), Names.ident(o.name.value))),
      names.map(LExpr.Name(_)))
    Decl.Theorem(List(Attr.FrflowDefs),
      Names.builtin(s"${className(m).text}.${LeanNames.ident(o.name.value + suffix)}"),
      names.zip(o.params).map((n, p) => LBinder.Explicit(n, LowerType.binder(p._2))),
      LExpr.Infix(LOp.Eq, LExpr.Typed(LExpr.Paren(own), monad), value(names)), Proof.Rfl, Break.NextLine)

  /** An operation's parameters' names, bound as every variable is (`Naming`): apart from every symbol, namespace and
    * name generated Lean writes itself.
    */
  def params(naming: Naming, o: OpSig): List[LeanName] =
    o.params.zipWithIndex.map { case ((p, t), i) => Binder(VarId.level(i), p, t) }.traverse(Naming.bind)
      .runA(naming).value
  def space(m: StateModel): LeanName = space(m.name)
  def space(m: ModelName): LeanName = Names.ident(m.value.capitalize)
  /** The class of a model's operations, in its namespace (`StoredBookings.Ops`): its methods are named as the
    * Definitions, beside the meanings' `do` blocks of the same names in the namespace.
    */
  def className(m: StateModel): LeanName = Names.builtin(s"${space(m).text}.Ops")
  def stateM(state: LExpr, result: Ty): LExpr = LExpr.App(name("StateM"), List(state, LowerType(result)))
