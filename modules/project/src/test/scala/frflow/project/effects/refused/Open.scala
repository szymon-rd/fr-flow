package frflow.project.effects.refused

/** A class another may extend: a call of its method may run another's. */
class Open:
  def one(): Int = 1
  def two(): Int = one() + 1
