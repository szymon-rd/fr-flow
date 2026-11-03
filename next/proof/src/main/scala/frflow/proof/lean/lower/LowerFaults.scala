package frflow.proof.lean.lower

import frflow.core.expr.{Expr, Prog, Progs}
import frflow.core.name.{ModelName, SymbolName}
import frflow.core.ty.Ty
import frflow.core.vocab.{DefineForm, OpSig, StateModel, Vocabulary}
import frflow.proof.lean.ast.*

/** The models' instances where programs may fail with `E` (the failing `Models.lean`): on
  * `ExceptT E (StateM World)`, a call of an operation of a model failing with `E` takes the next of the world's
  * faults and fails on `true` with the model's error, changing nothing else (`FrFlow.failing`); every other call is
  * lifted (`ExceptT.lift`). A model failing with another error has no instance there: a program calling it fails
  * with that one (`ErrorsDiffer`) or handles it, which this monad cannot run.
  */
final class LowerFaults(env: LowerEnv, naming: Naming):
  import Atoms.{const, name}

  /** Each error's instances and lemmas, the first's lemmas `_onWorldE`, the next's `_onWorldE1`, …. */
  def decls(models: List[StateModel], errors: List[Ty]): List[Decl] =
    errors.zipWithIndex.flatMap { (e, i) =>
      val suffix = if i == 0 then "_onWorldE" else s"_onWorldE$i"
      val over = models.filter(_.failsWith.forall(_ == e))
      over.map(instance(e, _)) ++ over.flatMap(m => m.sigs.map(o =>
        LowerModels.lemma((m, o), suffix, LExpr.App(monad(e), List(LowerType(o.result))), naming)(onWorld(e, m, o, _))))
    }

  private def instance(e: Ty, m: StateModel): Decl =
    Decl.Instance(LExpr.App(LExpr.Name(LowerModels.className(m)), List(LExpr.Paren(monad(e)))),
      m.sigs.map { o =>
        val ps = LowerModels.params(naming, o)
        InstanceField(Names.ident(o.name.value), ps, onWorld(e, m, o, ps))
      })

  /** `ExceptT E (StateM World)`. */
  private def monad(e: Ty): LExpr =
    LExpr.App(name("ExceptT"), List(LowerType(e), LExpr.Paren(LExpr.App(name("StateM"), List(name("World"))))))

  /** `FrFlow.failing (fun w => w.faults) (fun w s => { w with faults := s }) error (on the world)`, or
    * `ExceptT.lift (on the world)`.
    */
  private def onWorld(e: Ty, m: StateModel, o: OpSig, names: List[LeanName]): LExpr =
    val within = LExpr.Paren(LowerModels.onWorld(env, m, o, names))
    m.fails.filter(_.ty == e).fold(LExpr.App(const("ExceptT.lift"), List(within))) { f =>
      val (w, fs) = (Names.builtin("w"), Names.builtin("s"))
      val get = LExpr.Fun(List(LBinder.Bare(w)), LExpr.Dot(LExpr.Name(w), LowerFaults.field.text))
      val put = LExpr.Fun(List(LBinder.Bare(w), LBinder.Bare(fs)),
        LExpr.Update(LExpr.Name(w), List(LowerFaults.field -> LExpr.Name(fs))))
      val error = LowerValue(env)(f.error, f.ty).runA(naming).value
      LExpr.App(const("FrFlow.failing"), List(LExpr.Paren(get), LExpr.Paren(put), error, within))
    }

object LowerFaults:
  import Atoms.{const, name}
  /** The world's field of faults, which no model's field takes (`Reserved`). */
  val field: LeanName = Names.builtin("faults")
  val listOfBool: LExpr = LExpr.Paren(LExpr.App(Atoms.name("List"), List(Atoms.name("Bool"))))

  /** A race's winner as Lean reads it (`Prog.leftWins`): the scheduler's choice, `FrFlow.Races.leftWins`, which a
    * program racing two branches asks of its monad. On `StateM World` it is the next of the world's `races` (`true`:
    * the left wins; the left when none is left, as the Scala tests' sequential runs read it), the field the World has
    * when some program races; on `ExceptT E (StateM World)` it is lifted (the library's instance).
    */
  val leftWins: LExpr = const("FrFlow.Races.leftWins")
  /** A race's loser until the scheduler cancels it (`Prog.Cut`): `FrFlow.Races.cut (do …)`, the block in `OptionT`,
    * each of its steps `FrFlow.Races.step (…)`, the scheduler's choice first (`true`: it is cancelled before it).
    */
  val cut: LExpr = const("FrFlow.Races.cut")
  val cutStep: LExpr = const("FrFlow.Races.step")
  /** A loser's traverse at once: each branch cancelled at its own step, what follows dropped when one was. */
  val cutEach: LExpr = const("FrFlow.Races.each")
  /** The world's field of the scheduler's choices (the races' winners, and where their losers are cancelled), which
    * no model's field takes (`Reserved`).
    */
  val racesField: LeanName = Names.builtin("races")

  /** Whether some program of the vocabulary races two branches. */
  def racing(v: Vocabulary): Boolean = v.defines.filter(_.form == DefineForm.Flow).exists(d => d.lambda.body match
    case Expr.Do(p, _) => races(p)
    case _             => false)

  def races[E](p: Prog[E]): Boolean = Progs.operations(p).contains(Prog.leftWins)

  /** `[FrFlow.Races m]`: what a program racing asks of its monad `m`. */
  def racesBinder(m: LeanName): LBinder = LBinder.Instance(LExpr.App(const("FrFlow.Races"), List(LExpr.Name(m))))

  /** The instance on `StateM World`, and its lemma for `frflow_defs`. */
  def racesDecls: List[Decl] =
    val (w, s) = (Names.builtin("w"), Names.builtin("s"))
    val get = LExpr.Fun(List(LBinder.Bare(w)), LExpr.Dot(LExpr.Name(w), racesField.text))
    val put = LExpr.Fun(List(LBinder.Bare(w), LBinder.Bare(s)), LExpr.Update(LExpr.Name(w), List(racesField ->
      LExpr.Name(s))))
    val next = LExpr.App(const("FrFlow.nextRace"), List(LExpr.Paren(get), LExpr.Paren(put)))
    val monad = LExpr.App(name("StateM"), List(name("World")))
    List(Decl.Instance(LExpr.App(const("FrFlow.Races"), List(LExpr.Paren(monad))),
        List(InstanceField(Names.ident("leftWins"), Nil, next))),
      Decl.Theorem(List(Attr.FrflowDefs), Names.builtin("FrFlow.Races.leftWins_onWorld"), Nil,
        LExpr.Infix(LOp.Eq, LExpr.Typed(LExpr.Paren(leftWins), LExpr.App(monad, List(name("Bool")))), next),
        Proof.Rfl, Break.NextLine))

  /** The world's field of the time it lets pass at each of the clock's steps, in order (owner §47), which no model's
    * field takes (`Reserved`).
    */
  val ticksField: LeanName = Names.builtin("ticks")
  val listOfNat: LExpr = LExpr.Paren(LExpr.App(Atoms.name("List"), List(Atoms.name("Nat"))))
  /** A wait's end at once with others (`Prog.reach`), as a program asks it of its monad. */
  val reach: LExpr = const("FrFlow.Waits.reach")

  /** `[FrFlow.Waits m]`: what a program waiting at once asks of its monad `m`. */
  def waitsBinder(m: LeanName): LBinder = LBinder.Instance(LExpr.App(const("FrFlow.Waits"), List(LExpr.Name(m))))

  /** A clock's step on the World: the world's tick first (its `now` and `sleep`), and a move of the time (`sleep`,
    * `elapse`) taken where the schedules allow (owner §47); any other model's, as it is.
    */
  def timed(env: LowerEnv, m: ModelName, op: SymbolName, step: LExpr): LExpr = env.clock.filter(_.model == m)
    .fold(step) { c =>
      val (get, put) = field(env.modelField(m))
      val moved = if op == c.timed.now then step
        else LExpr.App(const("FrFlow.Clock.guard"), List(get, put, c.allows, LExpr.Paren(step)))
      if op == c.timed.elapse then moved else
        val (ticks, putTicks) = field(ticksField)
        LExpr.App(const("FrFlow.Clock.tick"), List(ticks, putTicks, get, put, c.allows, LExpr.Paren(moved)))
    }

  /** The clock's own declarations on the World: the instance a program waiting at once runs on, its lemma, and the
    * world's own step run on the World (`ClockModel.elapse_run`), what a statement and `cover_` read.
    */
  def clockDecls(env: LowerEnv, fields: List[LeanName]): List[Decl] = env.clock.toList.flatMap { c =>
    val (get, put) = field(env.modelField(c.model))
    val reachOn = LExpr.App(const("FrFlow.Clock.reach"), List(get, put, c.allows))
    val monad = LExpr.App(name("StateM"), List(name("World")))
    val (d, w) = (Names.builtin("x"), Names.builtin("w"))
    val elapse = LExpr.App(LExpr.Const(List(Names.builtin(s"${LowerModels.space(c.model).text}.Ops"),
      Names.ident(c.timed.elapse.value))), List(LExpr.Name(d)))
    List(Decl.Instance(LExpr.App(const("FrFlow.Waits"), List(LExpr.Paren(monad))),
        List(InstanceField(Names.ident("reach"), Nil, reachOn))),
      Decl.Theorem(List(Attr.FrflowDefs), Names.builtin("FrFlow.Waits.reach_onWorld"), Nil,
        LExpr.Infix(LOp.Eq, LExpr.Typed(LExpr.Paren(reach), LExpr.Infix(LOp.Arrow, name("Int"),
          LExpr.Infix(LOp.Arrow, name("Int"), LExpr.App(monad, List(name("Unit")))))), reachOn),
        Proof.Rfl, Break.NextLine),
      Decl.Def(List(Attr.FrflowDefs), Names.builtin(s"${LowerModels.space(c.model).text}.${
          LowerModels.runName(c.timed.elapse)}"), Nil,
        LExpr.Infix(LOp.Arrow, name("Int"), LExpr.Infix(LOp.Arrow, name("World"),
          LExpr.Paren(LExpr.Infix(LOp.Times, name("Unit"), name("World"))))),
        LExpr.Fun(List(LBinder.Explicit(d, name("Int")), LBinder.Explicit(w, name("World"))),
          LExpr.App(const("FrFlow.runOn"), List(LExpr.Typed(LExpr.Paren(elapse), LExpr.App(monad,
            List(name("Unit")))), LExpr.Name(w)))))) ++ passing(env, c, fields)
  }

  /** `World.ticked_f` and `World.move_f`: each other field of the World is as it was where the time passes, so a run
    * reads through it; and the clock's own, moved where the schedules allow.
    */
  private def passing(env: LowerEnv, c: LowerEnv.Clock, fields: List[LeanName]): List[Decl] =
    val clock = env.modelField(c.model)
    val ((get, put), (ticks, putTicks)) = (field(clock), field(ticksField))
    val (w, t) = (Names.builtin("w"), Names.builtin("s"))
    val ticked = LExpr.App(const("FrFlow.Clock.ticked"), List(ticks, putTicks, get, put, c.allows, LExpr.Name(w)))
    val moved = LExpr.App(const("FrFlow.Clock.move"), List(put, c.allows, LExpr.Name(t), LExpr.Name(w)))
    def same(f: LeanName, of: LExpr) = LExpr.Infix(LOp.Eq, LExpr.Dot(LExpr.Paren(of), f.text), LExpr.Dot(LExpr.Name(w),
      f.text))
    def lemma(n: String, ps: List[LBinder], st: LExpr, proof: List[String]) =
      Decl.Theorem(List(Attr.FrflowDefs), Names.builtin(n), ps, st, Proof.Tactics(proof), Break.NextLine)
    val world = LBinder.Explicit(w, name("World"))
    val time = LBinder.Explicit(t, name("Int"))
    val others = fields.filterNot(_ == clock)
    others.filterNot(_ == ticksField).map(f => lemma(s"World.ticked_${f.text}", List(world), same(f, ticked),
      List("unfold FrFlow.Clock.ticked FrFlow.Clock.move", "split <;> (try split) <;> rfl"))) ++
      others.map(f => lemma(s"World.move_${f.text}", List(time, world), same(f, moved),
        List("unfold FrFlow.Clock.move", "split <;> rfl"))) :+
      lemma(s"World.move_${clock.text}", List(time, world), LExpr.Infix(LOp.Eq, LExpr.Dot(LExpr.Paren(moved),
        clock.text), LExpr.If(LExpr.App(c.allows, List(LExpr.Name(w), LExpr.Name(t))), LExpr.Name(t),
        LExpr.Dot(LExpr.Name(w), clock.text))), List("unfold FrFlow.Clock.move", "split <;> simp_all"))

  /** `(fun w => w.f)` and `(fun w s => { w with f := s })`: a field of the World, read and put back. */
  private def field(f: LeanName): (LExpr, LExpr) =
    val (w, s) = (Names.builtin("w"), Names.builtin("s"))
    (LExpr.Paren(LExpr.Fun(List(LBinder.Bare(w)), LExpr.Dot(LExpr.Name(w), f.text))),
      LExpr.Paren(LExpr.Fun(List(LBinder.Bare(w), LBinder.Bare(s)), LExpr.Update(LExpr.Name(w), List(f ->
        LExpr.Name(s))))))
