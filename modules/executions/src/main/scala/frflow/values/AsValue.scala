package frflow.values

import frflow.*

/** A term of a statement as the value of the code it is. */
trait AsValue[A]:
  def apply(a: Term[A]): Term[Value]

object AsValue:
  given AsValue[Value] = a => a
  given [C]: AsValue[Ref[C]] = a => a.asValue
  given AsValue[Boolean] = a => make[Value.Bool](a)
  given AsValue[BigInt] = a => make[Value.Int](a)
  given AsValue[String] = a => make[Value.Str](a)
  given AsValue[Unit] = _ => Value.Unit
