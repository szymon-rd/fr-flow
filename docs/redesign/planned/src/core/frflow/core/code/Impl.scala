package frflow.core.code

/** Scala code the IR refers to but does not read (an implementation, a binding's value, how a boundary's
  * implementation is started): a handle that builds the function under the values in force. Only `eval.Fn` calls one.
  */
final class Impl(val arity: Int, val make: () => AnyRef)
