package frflow.dsl.flow

import frflow.core.name.BoundaryName
import frflow.core.vocab.{BoundarySig, Fails}
import frflow.dsl.build.{Declarations, Source}
import frflow.dsl.term.{LeanType, Reify, Term}

/** A boundary as a model declares it (`val database = Boundary[Database]("the SQLite database …")`, named as its
  * val): its trait of operations `B[F[_], T[_]]`, whose values are `T`: `Term` in programs and models, plain Scala in
  * an adapter (`B[IO, Id]`). Its operations (`BoundaryOps`) are derived from the trait (`trait Database[F[_], T[_]]
  * derives BoundaryOps`). A failing one says what a call fails with, and declares the error's type.
  */
final case class Boundary[B[_[_], _[_]]](name: BoundaryName, means: String, ops: BoundaryOps[B],
    fails: Option[Fails], declares: Declarations):
  /** The instance programs are recorded with: each call a `Recorded.Call`. */
  def recording: B[Recorded, Term] = ops.recording(name)
  def sig: BoundarySig = BoundarySig(name, ops.className, means, ops.ops, fails)

object Boundary:
  inline def apply[B[_[_], _[_]]](means: String)(using ops: BoundaryOps[B]): Boundary[B] =
    Boundary(BoundaryName(Source.valName), means, ops, None, Declarations.none)

  /** A boundary any call of which may fail, with `error` (a store that may be down, `Failure.StoreUnavailable`),
    * changing nothing.
    */
  inline def failing[B[_[_], _[_]], E](means: String, error: E)(using ops: BoundaryOps[B], e: LeanType[E])
      : Boundary[B] =
    Boundary(BoundaryName(Source.valName), means, ops, Some(fails(e, error)), e.declares)

  /** The error as a value of its type: a value of a type with a `LeanType` always reads as one. */
  def fails[E](e: LeanType[E], error: E): Fails = Reify(e, error).fold(
    f => throw IllegalStateException(s"FrFlow bug: a boundary's error read as no value: $f"), Fails(e.ty, _))
