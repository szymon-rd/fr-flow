package frflow
package kb

/** What keeps a FrModel from being checked, said so that its author can fix it. */
enum Problem(val message: String):
  case Structure(text: String) extends Problem(text)
  case Vocabulary(text: String) extends Problem(text)
  case Wording(text: String) extends Problem(text)
  case Examples(text: String) extends Problem(text)
  case Invariants(text: String) extends Problem(text)
  case Code(text: String) extends Problem(text)
  override def toString: String = message
