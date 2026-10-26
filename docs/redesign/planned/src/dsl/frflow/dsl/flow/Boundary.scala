package frflow.dsl.flow

import frflow.core.name.BoundaryName
import frflow.core.vocab.BoundarySig
import frflow.dsl.build.Source
import frflow.dsl.term.Term

/** A boundary as a model declares it (`val database = Boundary[Database]("the SQLite database …")`, named as its
  * val): its trait of operations `B[F[_], T[_]]`, whose values are `T`: `Term` in programs and models, plain Scala in
  * an adapter (`B[IO, Id]`). Its operations (`BoundaryOps`) are derived from the trait (`trait Database[F[_], T[_]]
  * derives BoundaryOps`).
  */
final case class Boundary[B[_[_], _[_]]](name: BoundaryName, means: String, ops: BoundaryOps[B]):
  /** The instance programs are recorded with: each call a `Recorded.Call`. */
  def recording: B[Recorded, Term] = ops.recording(name)
  def sig: BoundarySig = BoundarySig(name, ops.className, means, ops.ops, None)

object Boundary:
  inline def apply[B[_[_], _[_]]](means: String)(using ops: BoundaryOps[B]): Boundary[B] =
    Boundary(BoundaryName(Source.valName), means, ops)
