package frflow.dsl.flow

import frflow.core.name.BoundaryName
import frflow.core.vocab.BoundarySig
import frflow.dsl.build.Source
import frflow.core.ty.Ty
import frflow.dsl.term.{LeanType, Term}

/** A boundary as a model declares it (`val database = Boundary[Database]("the SQLite database …")`, named as its
  * val): its trait of operations `B[F[_], T[_]]`, whose values are `T`: `Term` in programs and models, plain Scala in
  * an adapter (`B[IO, Id]`). Its operations (`BoundaryOps`) are derived from the trait (`trait Database[F[_], T[_]]
  * derives BoundaryOps`).
  */
final case class Boundary[B[_[_], _[_]]](name: BoundaryName, means: String, ops: BoundaryOps[B],
    failsWith: Option[Ty]):
  /** The instance programs are recorded with: each call a `Recorded.Call`. */
  def recording: B[Recorded, Term] = ops.recording(name)
  def sig: BoundarySig = BoundarySig(name, ops.className, means, ops.ops, failsWith)

object Boundary:
  inline def apply[B[_[_], _[_]]](means: String)(using ops: BoundaryOps[B]): Boundary[B] =
    Boundary(BoundaryName(Source.valName), means, ops, None)

  /** A boundary any call of which may fail with an `E` (a store that may be down), changing nothing. */
  inline def failing[B[_[_], _[_]], E](means: String)(using ops: BoundaryOps[B], e: LeanType[E]): Boundary[B] =
    Boundary(BoundaryName(Source.valName), means, ops, Some(e.ty))
