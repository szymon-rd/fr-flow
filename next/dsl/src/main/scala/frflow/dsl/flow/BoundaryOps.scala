package frflow.dsl.flow

import cats.{Functor, Id}
import frflow.core.name.{BoundaryName, OpName}
import frflow.core.vocab.{ModelOp, OpSig}
import frflow.dsl.build.Declarations
import frflow.dsl.term.Term

/** A boundary trait's operations, derived at compile time from `B`'s methods (`derived`, a macro): their signatures
  * and the vocabulary their types declare, the three instances FrFlow makes of the trait, and a model read from the
  * developer's instance of it.
  */
trait BoundaryOps[B[_[_], _[_]]]:
  /** The trait's name, the Lean class's. */
  def className: String
  def ops: List[OpSig]
  def declares: Declarations
  /** Each operation a recorded call. */
  def recording(name: BoundaryName): B[Recorded, Term]
  /** An adapter's operation called by name on plain values: the model tests' generated runs. */
  def call[F[_]: Functor](adapter: B[F, Id], op: OpName, args: List[Any]): F[Any]
  /** An adapter as programs call it: each argument the value of its term, each result the term of its value. */
  def lifted[F[_]: Functor](adapter: B[F, Id], values: Terms): B[F, Term]
  /** A model (an instance over `Model`'s state, recorded): each operation's steps from its parameters' variables. */
  def model(instance: B[Recorded, Term]): List[ModelOp]

object BoundaryOps:
  /** `trait Database[F[_], T[_]] derives BoundaryOps`: a macro, not planned here (`RecordingSuite`'s `Store` and
    * rooms' `BookingsOps` are written as it will write them).
    */
  inline def derived[B[_[_], _[_]]]: BoundaryOps[B] = ${ BoundaryMacros.derived[B] }
