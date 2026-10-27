package frflow.eval.run

import cats.data.{State, StateT}
import cats.effect.kernel.Ref
import cats.syntax.all.*
import frflow.core.code.Impl
import frflow.core.expr.{Lambda, Prog}
import frflow.core.name.ModelName
import frflow.core.spec.Written
import frflow.core.term.{Program, Stated, World}
import frflow.core.vocab.Vocabulary
import frflow.eval.{Env, Faults, Fn, NotEvaluated, Races, ScalaValue, Semantics}
import frflow.eval.flow.{FlowError, FlowInterpreter, World as Worlds}

/** A proven program as the evaluator holds its value (`A => Program[R]`): its recorded steps run on the models from
  * the world before, one after the other as Lean reads them (`FlowInterpreter.sequential` over a pure state of the
  * models' states), its outcome and the world after, as Lean's `World → R × World`. What gives an example about a
  * run, and a generated test of a claim about one, its Scala value; production runs programs through `Running`.
  */
object ProgramRun:
  private type States = Map[ModelName, ScalaValue]
  private type Failing[A] = Either[Throwable, A]
  private type S[A] = StateT[Failing, States, A]

  def impl(semantics: Semantics, v: Vocabulary, w: Written[Lambda], steps: Prog[Stated[?]]): Impl =
    val arity = w.value.arity
    Impl(arity, values => Fn.of[AnyRef](arity)(args =>
      val env = w.value.params.zip(args).foldLeft(Env.of(values))((e, xa) => e.bind(xa._1.id, xa._2))
      ScalaValue(Program.of[Any](before => run(semantics, v, steps, env)(before)))))

  /** The run from `before`: its outcome (its error on the left) and the world after. */
  private def run(semantics: Semantics, v: Vocabulary, steps: Prog[Stated[?]], env: Env)(before: World)
      : (Either[Any, Any], World) =
    val held = (v.models.map(_.name) :+ Faults.model :+ Races.model)
      .flatMap(m => before.state(m).map(m -> ScalaValue(_))).toMap
    val interpreter = FlowInterpreter.sequential[S](semantics, Worlds.models[S](semantics, v, StatesRef))
    interpreter.outcome(steps, env).run(held) match
      case Right((end, out))               => (out.bimap(_.unwrap, _.unwrap), World.of(end.map((m, x) => m -> x.unwrap)))
      case Left(FlowError.NotEvaluated(e)) => throw NotEvaluated(e)
      case Left(other)                     => throw other

  /** The models' states as the state the run threads. */
  private object StatesRef extends Ref[S, States]:
    def get: S[States] = StateT.get
    def set(a: States): S[Unit] = StateT.set(a)
    def access: S[(States, States => S[Boolean])] = get.map(a => (a, b => set(b).as(true)))
    def tryUpdate(f: States => States): S[Boolean] = update(f).as(true)
    def tryModify[B](f: States => (States, B)): S[Option[B]] = modify(f).map(Some(_))
    def update(f: States => States): S[Unit] = StateT.modify(f)
    def modify[B](f: States => (States, B)): S[B] = StateT(s => Right(f(s)): Failing[(States, B)])
    def tryModifyState[B](state: State[States, B]): S[Option[B]] = modifyState(state).map(Some(_))
    def modifyState[B](state: State[States, B]): S[B] = modify(s => state.run(s).value)
