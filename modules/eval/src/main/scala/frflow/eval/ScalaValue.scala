package frflow.eval

/** A value as Scala holds it at run time. Untyped: the IR's types say what it is. */
opaque type ScalaValue = Any

object ScalaValue:
  def apply(a: Any): ScalaValue = a
  extension (v: ScalaValue) def unwrap: Any = v
