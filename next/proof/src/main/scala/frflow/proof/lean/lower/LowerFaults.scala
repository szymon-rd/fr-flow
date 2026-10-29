package frflow.proof.lean.lower

import frflow.core.ty.Ty
import frflow.core.vocab.{OpSig, StateModel}
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
        LowerModels.lemma((m, o), suffix, LExpr.App(monad(e), List(LowerType(o.result))), onWorld(e, m, o))))
    }

  private def instance(e: Ty, m: StateModel): Decl =
    Decl.Instance(LExpr.App(LExpr.Name(LowerModels.className(m)), List(LExpr.Paren(monad(e)))),
      m.sigs.map(o => InstanceField(Names.ident(o.name.value), LowerModels.params(o), onWorld(e, m, o))))

  /** `ExceptT E (StateM World)`. */
  private def monad(e: Ty): LExpr =
    LExpr.App(name("ExceptT"), List(LowerType(e), LExpr.Paren(LExpr.App(name("StateM"), List(name("World"))))))

  /** `FrFlow.failing (fun w => w.faults) (fun w s => { w with faults := s }) error (on the world)`, or
    * `ExceptT.lift (on the world)`.
    */
  private def onWorld(e: Ty, m: StateModel, o: OpSig): LExpr =
    val within = LExpr.Paren(LowerModels.onWorld(env, m, o))
    m.fails.filter(_.ty == e).fold(LExpr.App(const("ExceptT.lift"), List(within))) { f =>
      val (w, fs) = (Names.builtin("w"), Names.builtin("s"))
      val get = LExpr.Fun(List(LBinder.Bare(w)), LExpr.Dot(LExpr.Name(w), LowerFaults.field.text))
      val put = LExpr.Fun(List(LBinder.Bare(w), LBinder.Bare(fs)),
        LExpr.Update(LExpr.Name(w), List(LowerFaults.field -> LExpr.Name(fs))))
      val error = LowerValue(env)(f.error, f.ty).runA(naming).value
      LExpr.App(const("FrFlow.failing"), List(LExpr.Paren(get), LExpr.Paren(put), error, within))
    }

object LowerFaults:
  /** The world's field of faults, which no model's field takes (`Reserved`). */
  val field: LeanName = Names.builtin("faults")
  val listOfBool: LExpr = LExpr.Paren(LExpr.App(Atoms.name("List"), List(Atoms.name("Bool"))))
