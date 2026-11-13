package frflow.dsl.structure

import frflow.core.name.TypeName
import frflow.core.ty.Ty
import frflow.dsl.term.RocqType
import scala.compiletime.constValue

/** What a statement's terms about a structure whole are typed by (`limits.State`, the structure after a call, a step
  * of a call): the structure's name. Not the structure's trait: Scala's capture checking reads a `caps.Mutable` trait
  * named in a type as a capability, which a term is not.
  */
final class State[N <: String] private ()

object State:
  /** The structure's type in the model: named as its trait. */
  inline given named[N <: String]: RocqType[State[N]] = typed[State[N]](constValue[N])

  /** The type of a structure's states by the structure's name: a statement needs no more of it. */
  def typed[A](name: String): RocqType[A] = RocqType.of[A](Ty.Data(TypeName(name)))
