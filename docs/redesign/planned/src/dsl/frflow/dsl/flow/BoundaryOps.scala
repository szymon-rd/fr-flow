package frflow.dsl.flow

import frflow.core.name.OpName
import frflow.core.vocab.OpSig
import frflow.dsl.build.Declarations
import frflow.dsl.term.Term

/** A boundary trait's operations, derived at compile time from `T`'s methods (`derived`, a macro): their signatures
  * and the vocabulary their types declare (no Java reflection on types, no registry), and how to call one on an
  * implementation.
  */
trait BoundaryOps[T]:
  def ops: List[OpSig]
  def declares: Declarations
  def call(impl: T, op: OpName, args: List[Term[Any]]): Flow[Any]

object BoundaryOps:
  inline given derived[T]: BoundaryOps[T] = ${ BoundaryMacros.derived[T] }
