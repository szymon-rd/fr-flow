package frflow.dsl.term

import frflow.core.expr.Value
import frflow.dsl.build.Fault

/** A Scala value as a `Value`, walked by its type through the `DataRep`s its `LeanType` declares. */
object Reify:
  def apply[A](t: LeanType[A], a: A): Either[Fault, Value] = ???
