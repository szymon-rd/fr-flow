package frflow.dsl.flow

import cats.syntax.all.*
import frflow.core.name.{BoundaryName, OpName}
import frflow.dsl.flow.Recording.given
import frflow.dsl.term.{LeanType, Term}

/** A boundary of the tests, and FrFlow's clock, with the recording instances `BoundaryOps.derived` will make. */
trait Store[F[_], T[_]]:
  def load: F[T[BigInt]]
  def save(n: T[BigInt]): F[Unit]

object Store:
  private def call[R: LeanType](b: String, op: String, args: Term[?]*): Recorded[Term[R]] =
    Recorded.Call(BoundaryName(b), OpName(op), args.toList, LeanType[R])

  val recording: Store[Recorded, Term] = new Store[Recorded, Term]:
    def load: Recorded[Term[BigInt]] = call("store", "load")
    def save(n: Term[BigInt]): Recorded[Unit] = call[Unit]("store", "save", n).void

  val clock: Clock[Recorded, Term] = new Clock[Recorded, Term]:
    def now: Recorded[Term[BigInt]] = call("clock", "now")
    def sleep(seconds: Term[BigInt]): Recorded[Unit] = call[Unit]("clock", "sleep", seconds).void
