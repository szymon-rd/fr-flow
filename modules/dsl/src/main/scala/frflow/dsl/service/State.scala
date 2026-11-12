package frflow.dsl.service

import frflow.core.name.TypeName
import frflow.core.ty.Ty
import frflow.dsl.term.LeanType
import scala.compiletime.constValue

/** What a statement's terms about a service whole are typed by (`limits.State`, the service after a call, a step
  * of a call): the service's name. Not the service's trait: Scala's capture checking reads a `caps.Mutable` trait
  * named in a type as a capability, which a term is not.
  */
final class State[N <: String] private ()

object State:
  /** The service's type in the model: named as its trait. */
  inline given named[N <: String]: LeanType[State[N]] = typed[State[N]](constValue[N])

  /** The type of a service's states by the service's name: a statement needs no more of it. */
  def typed[A](name: String): LeanType[A] = LeanType.of[A](Ty.Data(TypeName(name)))
