package frflow.dsl.flow

import cats.{Functor, Id, MonadThrow}
import cats.syntax.all.*
import frflow.core.expr.Binder
import frflow.core.name.{BoundaryName, OpName, VarId}
import frflow.core.ty.{NumKind, Ty}
import frflow.core.vocab.{Fails, ModelOp, OpSig}
import frflow.dsl.build.Declarations
import frflow.dsl.term.{LeanType, Term}

/** The clock's operations, written as `derives BoundaryOps` writes them: a macro does not expand in the module that
  * defines it, and the clock is this module's own boundary (checked against the derivation in the tests).
  */
object ClockOps extends BoundaryOps[Clock]:
  private val seconds = Ty.Num(NumKind.Big)

  def className: String = "Clock"
  def ops: List[OpSig] = List(OpSig(OpName("now"), Nil, seconds), OpSig(OpName("sleep"), List("seconds" -> seconds),
    Ty.Unit))
  def declares: Declarations = Declarations.none

  def recording(name: BoundaryName): Clock[Recorded, Term] = new Clock[Recorded, Term]:
    def now: Recorded[Term[BigInt]] = Recorded.Call(name, OpName("now"), Nil, LeanType[BigInt])
    def sleep(seconds: Term[BigInt]): Recorded[Unit] =
      Recorded.Bind(Recorded.Call(name, OpName("sleep"), List(seconds), LeanType[Unit]), (_: Any) => Recorded.Pure(()))

  def call[F[_]: Functor](adapter: Clock[F, Id], op: OpName, args: List[Any]): F[Any] = (op.value, args) match
    case ("now", Nil)                 => adapter.now.widen
    case ("sleep", List(s: BigInt))   => adapter.sleep(s).widen
    case _                            => throw IllegalArgumentException(s"FrFlow: no ${op.value} on Clock")

  def lifted[F[_]](adapter: Clock[F, Id], values: Terms, fails: Option[Fails])(using F: MonadThrow[F])
      : Clock[F, Term] = new Clock[F, Term]:
    def now: F[Term[BigInt]] = called(adapter.now).map(values.term(_))
    def sleep(s: Term[BigInt]): F[Unit] = F.catchNonFatal(values.value(s)).flatMap(t => called(adapter.sleep(t)))
    private def called[A](fa: => F[A]): F[A] = BoundaryOps.failures(fails, values.fail)(F.unit.flatMap(_ => fa))

  def model(instance: Clock[Recorded, Term]): List[ModelOp] =
    val s = Binder(VarId.level(0), "seconds", seconds)
    List(ModelOp(OpName("now"), Nil, ReadRecording.steps(instance.now)._1),
      ModelOp(OpName("sleep"), List(s), ReadRecording.steps(instance.sleep(Term.free(s)))._1))
