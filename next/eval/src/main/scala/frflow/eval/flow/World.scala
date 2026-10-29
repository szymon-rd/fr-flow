package frflow.eval.flow

import cats.MonadThrow
import cats.effect.kernel.Ref
import cats.syntax.all.*
import frflow.core.expr.Prog
import frflow.core.name.{ModelName, SymbolName}
import frflow.core.term.Stated
import frflow.core.vocab.{Fails, Vocabulary}
import frflow.eval.{EvalError, Faults, Races, Raised, ScalaValue, Semantics}

/** Where a program's calls go when its `Prog` is run in Scala: the models (each call its operation's meaning, over
  * each model's state), or the operations' Scala (`Bound`, each argument and result a plain value).
  */
trait World[F[_]]:
  def call(op: SymbolName, args: List[ScalaValue]): F[ScalaValue]
  def read(model: ModelName): F[ScalaValue]
  def write(model: ModelName, state: ScalaValue): F[Unit]

object World:
  /** The models: each call its operation's meaning (`StateModel`), run by the evaluator over the models' states in
    * `states` (each model's state, by name, and the faults under `Faults.model`). A call of an operation of a model
    * that may fail takes the next of the faults, as Lean's `FrFlow.failing` does: `true` fails it with the model's
    * error, changing nothing else. A race's winner is the next of the races (`Races`). What a program runs on in
    * Scala, and what `ModelTests` compares the operations' Scala with.
    */
  def models[F[_]](semantics: Semantics, v: Vocabulary, states: Ref[F, Map[ModelName, ScalaValue]])(
      using F: MonadThrow[F]): World[F] = watched(semantics, v, states, (_, _, _) => F.unit)

  /** The models, each branch their steps take said to `branched`, with the operation it is in. */
  def watched[F[_]](semantics: Semantics, v: Vocabulary, states: Ref[F, Map[ModelName, ScalaValue]],
      branched: (SymbolName, Prog[Stated[?]], Boolean) => F[Unit])(using F: MonadThrow[F]): World[F] = new World[F]:
    self =>
    def read(m: ModelName): F[ScalaValue] =
      states.get.flatMap(_.get(m).liftTo[F](FlowError.NotEvaluated(EvalError.NoModel(m))))
    def write(m: ModelName, s: ScalaValue): F[Unit] = states.update(_.updated(m, s))
    def call(op: SymbolName, args: List[ScalaValue]): F[ScalaValue] =
      if Races.asks(op) then states.modify(Races.next).map(ScalaValue(_))
      else v.modelOf(op).flatMap(_.fails).fold(ran(op, args))(e =>
        states.modify(Faults.next).flatMap(fails => if fails then failed(e) else ran(op, args)))

    private def ran(op: SymbolName, args: List[ScalaValue]): F[ScalaValue] =
      v.modelOf(op).flatMap(_.op(op)).liftTo[F](FlowError.NoOperation(op))
        .flatMap(o => FlowInterpreter.watched(semantics, self, (p, held) => branched(op, p, held))
          .prog(o.steps, FlowInterpreter.arguments(o.params, args)))
    private def failed(e: Fails): F[ScalaValue] = F.raiseError(Raised(semantics.literal(e.error, e.ty), e.ty))

  /** The operations' Scala: each call its bound function on plain values, a failing model's failure its error
    * (`fail`); no model state.
    */
  def implemented[F[_]](ops: Map[SymbolName, Bound[F]], fail: (Fails, Throwable) => Throwable)(
      using F: MonadThrow[F]): World[F] = new World[F]:
    def call(op: SymbolName, args: List[ScalaValue]): F[ScalaValue] =
      ops.get(op).liftTo[F](FlowError.NoOperation(op)).flatMap(b =>
        Bound.failures(b.fails, fail)(F.unit.flatMap(_ => b.call(args.map(_.unwrap)))).map(ScalaValue(_)))
    def read(m: ModelName): F[ScalaValue] = F.raiseError(IllegalStateException("the operations' Scala has no model"))
    def write(m: ModelName, s: ScalaValue): F[Unit] = F.raiseError(IllegalStateException("no model state"))
