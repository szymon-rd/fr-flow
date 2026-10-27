package frflow.proof.lean.lower

import cats.syntax.all.*
import frflow.core.name.{DefName, SymbolName}
import frflow.core.ty.Ty
import frflow.core.vocab.{BoundarySig, Define, OpSig, StateModel}
import frflow.proof.lean.ast.*

/** The boundaries and their models as Lean (today's `Boundaries.lean`): each boundary's class; each model's operations
  * on its state, a `do` block of the steps the developer's model records (`LowerProg`); the `World` the models are
  * parts of; each class's instance on `StateM World` and its lemmas. And a program's run on the models (`f_run`),
  * what `impl` is asked of.
  */
final class LowerModels(env: LowerEnv, naming: Naming):
  import Atoms.{call, const, name}

  def decls(worlds: List[(BoundarySig, StateModel)]): List[Decl] =
    worlds.map((b, _) => classOf(b)) ++ worlds.map(model(_, _)) ++ List(world(worlds.map(_._2))) ++
      worlds.map(instance(_, _)) ++ worlds.flatMap(lemmas(_, _))

  /** `def f_run (open terms) : A → World → (R × World) := fun a w => (FrFlow.runOn ((K.f open terms) a) w)`. */
  def run(d: Define, flow: DefName, opens: List[(SymbolName, Ty)]): Decl =
    val inputs = d.lambda.params
    val result = d.lambda.result match
      case Ty.FlowOf(r) => r
      case other        => other
    val (n, names) = inputs.traverse(Naming.bind).run(naming).value
    val w = Naming.helper("w", Set.empty).runA(n).value
    val ran = names.foldLeft(Atoms.define(env, flow))((f, a) => call(f, List(LExpr.Name(a))))
    Decl.Def(List(Attr.FrflowDefs), Names.ident(d.name.value), opens.map((s, t) => typed(Names.ident(s.value), t)),
      LowerType.declaration(inputs.map(_.ty) :+ Ty.World, pairWithWorld(result)),
      LExpr.Fun(inputs.zip(names).map((x, a) => typed(a, x.ty)) :+ LBinder.Explicit(w, name("World")),
        call(const("FrFlow.runOn"), List(ran, LExpr.Name(w)))))

  /** `namespace Stored def inRoom_of (room : String) (s : (List Booking)) : RoomBookings := Id.run ((Stored.inRoom
    * room).run' s)`: a store operation's result on its model's state, which `made_<op>` is stated of.
    */
  def resultOf(m: StateModel, o: OpSig): Decl =
    val s = Names.builtin("s")
    val op = LExpr.App(LExpr.Const(List(modelName(m), Names.ident(o.name.value))), params(o).map(LExpr.Name(_)))
    val ran = LExpr.App(LExpr.Dot(LExpr.Paren(op), "run'"), List(LExpr.Name(s)))
    Decl.Namespace(List(modelName(m)), List(Decl.Def(List(Attr.FrflowDefs), Names.ident(s"${o.name.value}_of"),
      o.params.map((p, t) => typed(Names.ident(p), t)) :+ typed(s, m.state), LowerType(o.result),
      LExpr.App(const("Id.run"), List(LExpr.Paren(ran))))))

  private def classOf(b: BoundarySig): Decl =
    val monad = Names.builtin("m")
    Decl.Documented(s"The boundary ${b.name.value}: ${b.means}", Decl.Class(Names.builtin(b.className),
      List(LBinder.Explicit(monad, LExpr.Infix(LOp.Arrow, name("Type"), name("Type")))),
      b.ops.map(o => Names.ident(o.name.value) ->
        LowerType.declaration(o.params.map(_._2), LExpr.App(LExpr.Name(monad), List(LowerType(o.result)))))))

  private def model(b: BoundarySig, m: StateModel): Decl =
    Decl.Namespace(List(modelName(m)), m.ops.flatMap(op => b.ops.find(_.name == op.op).map { sig =>
      val (bs, lines) = (op.params.traverse(x => Naming.bind(x).map(typed(_, x.ty))),
        LowerProg(env, op.params.size).block(op.steps)).tupled.runA(naming).value
      val body = if bs.isEmpty then LExpr.Do(lines, 4) else LExpr.Fun(bs, LExpr.Do(lines, 4))
      Decl.Def(List(Attr.FrflowDefs), Names.ident(sig.name.value), Nil,
        LowerType.declaration(sig.params.map(_._2), stateM(LowerType(m.state), sig.result)), body)
    }))

  private def world(models: List[StateModel]): Decl =
    Decl.Documented("The models' states: what proven flows run on.",
      Decl.Structure(Names.builtin("World"), models.map(m => env.modelField(m.name) -> LowerType(m.state))))

  private def instance(b: BoundarySig, m: StateModel): Decl =
    Decl.Instance(LExpr.App(name(b.className), List(LExpr.Paren(LExpr.App(name("StateM"), List(name("World")))))),
      b.ops.map(o => InstanceField(Names.ident(o.name.value), params(o), onWorld(m, o))))

  private def lemmas(b: BoundarySig, m: StateModel): List[Decl] = b.ops.map { o =>
    val own = LExpr.App(Atoms.const(s"${b.className}.${o.name.value}"), params(o).map(LExpr.Name(_)))
    Decl.Theorem(List(Attr.FrflowDefs), Names.builtin(s"${b.className}.${o.name.value}_onWorld"),
      o.params.map((p, t) => typed(Names.ident(p), t)),
      LExpr.Infix(LOp.Eq, LExpr.Typed(LExpr.Paren(own), stateM(name("World"), o.result)), onWorld(m, o)), Proof.Rfl,
      Break.NextLine)
  }

  /** `FrFlow.within (fun w => w.f) (fun w s => { w with f := s }) (Model.op args)`: the model's operation on its
    * part of the world.
    */
  private def onWorld(m: StateModel, o: OpSig): LExpr =
    val (w, s, field) = (Names.builtin("w"), Names.builtin("s"), env.modelField(m.name))
    val get = LExpr.Fun(List(LBinder.Bare(w)), LExpr.Dot(LExpr.Name(w), field.text))
    val update = LExpr.Update(LExpr.Name(w), List(field -> LExpr.Name(s)))
    val set = LExpr.Fun(List(LBinder.Bare(w), LBinder.Bare(s)), update)
    val op = LExpr.App(LExpr.Const(List(modelName(m), Names.ident(o.name.value))), params(o).map(LExpr.Name(_)))
    LExpr.App(const("FrFlow.within"), List(LExpr.Paren(get), LExpr.Paren(set), LExpr.Paren(op)))

  private def params(o: OpSig): List[LeanName] = o.params.map(p => Names.ident(p._1))
  private def modelName(m: StateModel): LeanName = Names.ident(m.name.value.capitalize)
  private def stateM(state: LExpr, result: Ty): LExpr = LExpr.App(name("StateM"), List(state, LowerType(result)))
  private def pairWithWorld(r: Ty): LExpr = LExpr.Paren(LExpr.Infix(LOp.Times, LowerType(r), name("World")))
  private def typed(n: LeanName, t: Ty): LBinder = LBinder.Explicit(n, LowerType.binder(t))
