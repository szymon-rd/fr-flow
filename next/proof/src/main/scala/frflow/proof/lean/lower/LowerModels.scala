package frflow.proof.lean.lower

import cats.syntax.all.*
import frflow.core.name.{DefName, SymbolName}
import frflow.core.ty.Ty
import frflow.core.vocab.{Define, OpSig, StateModel}
import frflow.proof.lean.ast.*

/** The models as Lean (`Models.lean`): each model's class of its operations (`Stored.Ops`, the operations named as
  * their Definitions); each operation's meaning on the model's state, a `do` block of the steps its `means` records
  * (`LowerProg`); the `World` the models are parts of, with the faults the failing models' calls take; each class's
  * instance on `StateM World` and its lemmas, and on `ExceptT E (StateM World)` for each error `E` a program fails
  * with (`LowerFaults`). And a program's run on the models (`f_run`), what `impl` is asked of.
  */
final class LowerModels(env: LowerEnv, naming: Naming):
  import Atoms.{call, const, name}
  private val faults = LowerFaults(env, naming)

  def decls(models: List[StateModel], errors: List[Ty]): List[Decl] =
    models.map(classOf) ++ models.map(model) ++ List(world(models)) ++ models.map(instance) ++
      models.flatMap(lemmas) ++ faults.decls(models, errors)

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
    Decl.Def(List(Attr.FrflowDefs), Names.ident(d.name.value), opens.map((s, t) => typed(Names.ident(s.value), t)),
      LowerType.declaration(inputs.map(_.ty) :+ Ty.World, pairWithWorld(outcome)),
      LExpr.Fun(inputs.zip(names).map((x, a) => typed(a, x.ty)) :+ LBinder.Explicit(w, name("World")),
        call(runOn, List(ran, LExpr.Name(w)))))

  /** `namespace Stored def inRoom_of (room : String) (s : (List Booking)) : RoomBookings := Id.run ((Stored.inRoom
    * room).run' s)`: an operation's result on its model's state, which `made_<op>` is stated of.
    */
  def resultOf(m: StateModel, o: OpSig): Decl =
    val s = Names.builtin("s")
    val op = LExpr.App(LExpr.Const(List(LowerModels.space(m), Names.ident(o.name.value))),
      LowerModels.params(o).map(LExpr.Name(_)))
    val ran = LExpr.App(LExpr.Dot(LExpr.Paren(op), "run'"), List(LExpr.Name(s)))
    Decl.Namespace(List(LowerModels.space(m)), List(Decl.Def(List(Attr.FrflowDefs),
      Names.ident(s"${o.name.value}_of"), o.params.map((p, t) => typed(Names.ident(p), t)) :+ typed(s, m.state),
      LowerType(o.result), LExpr.App(const("Id.run"), List(LExpr.Paren(ran))))))

  private def classOf(m: StateModel): Decl =
    val monad = Naming.helper("m", Set.empty).runA(naming).value
    Decl.Documented(s"The operations on ${m.name.value}: ${m.means}", Decl.Class(LowerModels.className(m),
      List(LBinder.Explicit(monad, LExpr.Infix(LOp.Arrow, name("Type"), name("Type")))),
      m.sigs.map(o => Names.ident(o.name.value) ->
        LowerType.declaration(o.params.map(_._2), LExpr.App(LExpr.Name(monad), List(LowerType(o.result)))))))

  /** `namespace Stored`: each operation's meaning, a `do` block on the model's state. */
  def model(m: StateModel): Decl =
    Decl.Namespace(List(LowerModels.space(m)), m.ops.map { op =>
      val (bs, lines) = (op.params.traverse(x => Naming.bind(x).map(typed(_, x.ty))),
        LowerProg(env, op.params.size).block(op.steps)).tupled.runA(naming).value
      val body = if bs.isEmpty then LExpr.Do(lines, 4) else LExpr.Fun(bs, LExpr.Do(lines, 4))
      Decl.Def(List(Attr.FrflowDefs), Names.ident(op.op.value), Nil,
        LowerType.declaration(op.params.map(_.ty), LowerModels.stateM(LowerType(m.state), op.result)), body)
    })

  /** The models' states, and the faults when a model's operations may fail (`true`: that call fails, in order). */
  private def world(models: List[StateModel]): Decl =
    val failing = Option.when(models.exists(_.fails.nonEmpty))(LowerFaults.field -> LowerFaults.listOfBool)
    Decl.Documented("The models' states: what proven flows run on.", Decl.Structure(Names.builtin("World"),
      models.map(m => env.modelField(m.name) -> LowerType(m.state)) ++ failing))

  private def instance(m: StateModel): Decl =
    Decl.Instance(LExpr.App(LExpr.Name(LowerModels.className(m)),
      List(LExpr.Paren(LExpr.App(name("StateM"), List(name("World")))))),
      m.sigs.map(o => InstanceField(Names.ident(o.name.value), LowerModels.params(o), LowerModels.onWorld(env, m, o))))

  private def lemmas(m: StateModel): List[Decl] =
    m.sigs.map(o => LowerModels.lemma((m, o), "_onWorld", LowerModels.stateM(name("World"), o.result),
      LowerModels.onWorld(env, m, o)))

  private def pairWithWorld(r: Ty): LExpr = LExpr.Paren(LExpr.Infix(LOp.Times, LowerType(r), name("World")))
  private def typed(n: LeanName, t: Ty): LBinder = LBinder.Explicit(n, LowerType.binder(t))

object LowerModels:
  import Atoms.{const, name}

  /** `FrFlow.within (fun w => w.f) (fun w s => { w with f := s }) (Model.op args)`: the model's operation on its
    * part of the world.
    */
  def onWorld(env: LowerEnv, m: StateModel, o: OpSig): LExpr =
    val (w, s, field) = (Names.builtin("w"), Names.builtin("s"), env.modelField(m.name))
    val get = LExpr.Fun(List(LBinder.Bare(w)), LExpr.Dot(LExpr.Name(w), field.text))
    val update = LExpr.Update(LExpr.Name(w), List(field -> LExpr.Name(s)))
    val set = LExpr.Fun(List(LBinder.Bare(w), LBinder.Bare(s)), update)
    val op = LExpr.App(LExpr.Const(List(space(m), Names.ident(o.name.value))), params(o).map(LExpr.Name(_)))
    LExpr.App(const("FrFlow.within"), List(LExpr.Paren(get), LExpr.Paren(set), LExpr.Paren(op)))

  /** `@[frflow_defs] theorem Class.op_<suffix> (params) : ((Class.op args) : monad) = value := rfl`. */
  def lemma(op: (StateModel, OpSig), suffix: String, monad: LExpr, value: LExpr): Decl =
    val (m, o) = op
    val own = LExpr.App(const(s"${className(m).text}.${o.name.value}"), params(o).map(LExpr.Name(_)))
    Decl.Theorem(List(Attr.FrflowDefs), Names.builtin(s"${className(m).text}.${o.name.value}$suffix"),
      o.params.map((p, t) => LBinder.Explicit(Names.ident(p), LowerType.binder(t))),
      LExpr.Infix(LOp.Eq, LExpr.Typed(LExpr.Paren(own), monad), value), Proof.Rfl, Break.NextLine)

  def params(o: OpSig): List[LeanName] = o.params.map(p => Names.ident(p._1))
  def space(m: StateModel): LeanName = Names.ident(m.name.value.capitalize)
  /** The class of a model's operations, in its namespace (`StoredBookings.Ops`): its methods are named as the
    * Definitions, beside the meanings' `do` blocks of the same names in the namespace.
    */
  def className(m: StateModel): LeanName = Names.builtin(s"${space(m).text}.Ops")
  def stateM(state: LExpr, result: Ty): LExpr = LExpr.App(name("StateM"), List(state, LowerType(result)))
