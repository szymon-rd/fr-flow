package frflow.core.code

/** An implementation of a boundary run against its model: how it is started holding a state, and read back. */
final case class Realization(how: Realizes, start: Impl, read: Impl, runs: ScalaCode)
