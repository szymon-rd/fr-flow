package frflow
package types

/** `label` as Scala names it; `lean`, the constructor's Lean name; a singleton's value; making one from its fields. */
private[frflow] final class Ctor(val label: String, val lean: String, val fields: List[(String, LeanType[?])],
    val singleton: Option[Any], val make: List[Any] => Any)
