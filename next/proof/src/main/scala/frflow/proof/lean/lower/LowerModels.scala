package frflow.proof.lean.lower

import cats.syntax.all.*
import frflow.core.name.{DefName, SymbolName}
import frflow.core.ty.Ty
import frflow.core.vocab.{BoundarySig, Define, OpSig, StateModel}
import frflow.proof.lean.ast.*

/** The boundaries and their models as Lean (today's `Boundaries.lean`): each boundary's class; each model's operations
  * on its state, a `do` block of the steps the developer's model records (`LowerProg`); the `World` the models are
  * parts of, with the faults the failing boundaries' calls take; each class's instance on `StateM World` and its
  * lemmas, and on `ExceptT E (StateM World)` for each error `E` a program fails with (`LowerFaults`). And a program's
  * run on the models (`f_run`), what `impl` is asked of.
  */
final class LowerModels(env: LowerEnv, naming: Naming):
  import Atoms.{call, const, name}
  private val faults = LowerFaults(env, naming)

  def decls(worlds: List[(BoundarySig, StateModel)], errors: List[Ty]): List[Decl] =
    worlds.map((b, _) => classOf(b)) ++ worlds.map(model(_, _)) ++ List(world(worlds)) ++
      worlds.map(instance(_, _)) ++ worlds.flatMap(lemmas(_, _)) ++ faults.decls(worlds, errors)

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
    * room).run' s)`: a store operation's result on its model's state, which `made_<op>` is stated of.
    */
  def resultOf(m: StateModel, o: OpSig): Decl =
    val s = Names.builtin("s")
    val op = LExpr.App(LExpr.Const(List(LowerModels.space(m), Names.ident(o.name.value))),
      LowerModels.params(o).map(LExpr.Name(_)))
    val ran = LExpr.App(LExpr.Dot(LExpr.Paren(op), "run'"), List(LExpr.Name(s)))
    Decl.Namespace(List(LowerModels.space(m)), List(Decl.Def(List(Attr.FrflowDefs),
      Names.ident(s"${o.name.value}_of"), o.params.map((p, t) => typed(Names.ident(p), t)) :+ typed(s, m.state),
      LowerType(o.result), LExpr.App(const("Id.run"), List(LExpr.Paren(ran))))))

  private def classOf(b: BoundarySig): Decl =
    val monad = Naming.helper("m", Set.empty).runA(naming).value
    Decl.Documented(s"The boundary ${b.name.value}: ${b.means}", Decl.Class(Names.builtin(b.className),
      List(LBinder.Explicit(monad, LExpr.Infix(LOp.Arrow, name("Type"), name("Type")))),
      b.ops.map(o => Names.ident(o.name.value) ->
        LowerType.declaration(o.params.map(_._2), LExpr.App(LExpr.Name(monad), List(LowerType(o.result)))))))

  /** `namespace Stored`: each operation of the model, a `do` block on its state. */
  def model(b: BoundarySig, m: StateModel): Decl =
    Decl.Namespace(List(LowerModels.space(m)), m.ops.flatMap(op => b.ops.find(_.name == op.op).map { sig =>
      val (bs, lines) = (op.params.traverse(x => Naming.bind(x).map(typed(_, x.ty))),
        LowerProg(env, op.params.size).block(op.steps)).tupled.runA(naming).value
      val body = if bs.isEmpty then LExpr.Do(lines, 4) else LExpr.Fun(bs, LExpr.Do(lines, 4))
      Decl.Def(List(Attr.FrflowDefs), Names.ident(sig.name.value), Nil,
        LowerType.declaration(sig.params.map(_._2), LowerModels.stateM(LowerType(m.state), sig.result)), body)
    }))

  /** The models' states, and the faults when a boundary may fail (`true`: that call fails, in order). */
  private def world(worlds: List[(BoundarySig, StateModel)]): Decl =
    val failing = Option.when(worlds.exists(_._1.fails.nonEmpty))(LowerFaults.field -> LowerFaults.listOfBool)
    Decl.Documented("The models' states: what proven flows run on.", Decl.Structure(Names.builtin("World"),
      worlds.map((_, m) => env.modelField(m.name) -> LowerType(m.state)) ++ failing))

  private def instance(b: BoundarySig, m: StateModel): Decl =
    Decl.Instance(LExpr.App(name(b.className), List(LExpr.Paren(LExpr.App(name("StateM"), List(name("World")))))),
      b.ops.map(o => InstanceField(Names.ident(o.name.value), LowerModels.params(o), LowerModels.onWorld(env, m, o))))

  private def lemmas(b: BoundarySig, m: StateModel): List[Decl] =
    b.ops.map(o => LowerModels.lemma((b, o), "_onWorld", LowerModels.stateM(name("World"), o.result),
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
  def lemma(op: (BoundarySig, OpSig), suffix: String, monad: LExpr, value: LExpr): Decl =
    val (b, o) = op
    val own = LExpr.App(const(s"${b.className}.${o.name.value}"), params(o).map(LExpr.Name(_)))
    Decl.Theorem(List(Attr.FrflowDefs), Names.builtin(s"${b.className}.${o.name.value}$suffix"),
      o.params.map((p, t) => LBinder.Explicit(Names.ident(p), LowerType.binder(t))),
      LExpr.Infix(LOp.Eq, LExpr.Typed(LExpr.Paren(own), monad), value), Proof.Rfl, Break.NextLine)

  def params(o: OpSig): List[LeanName] = o.params.map(p => Names.ident(p._1))
  def space(m: StateModel): LeanName = Names.ident(m.name.value.capitalize)
  def stateM(state: LExpr, result: Ty): LExpr = LExpr.App(name("StateM"), List(state, LowerType(result)))
