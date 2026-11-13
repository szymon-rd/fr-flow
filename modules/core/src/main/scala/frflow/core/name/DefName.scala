package frflow.core.name

/** The name of a `define`: the Scala val it is assigned to, and its definition in Rocq. */
opaque type DefName = String

object DefName extends Label[DefName]
