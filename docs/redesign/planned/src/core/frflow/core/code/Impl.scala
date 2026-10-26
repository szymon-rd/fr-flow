package frflow.core.code

/** Scala code the IR refers to but does not read (an implementation, a given's value, how a boundary's
  * implementation is started): a handle that builds the function from the values it is given. Only `eval.Fn` calls
  * what it builds.
  */
final class Impl(val arity: Int, val make: Values => AnyRef)
