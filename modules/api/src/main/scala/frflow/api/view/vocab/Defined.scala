package frflow.api.view.vocab

import frflow.core.name.DefName

/** A define: what it means (its Scaladoc, when it has one), its source as written, and its Lean as FrFlow prints it. */
final case class Defined(name: DefName, means: Option[String], written: String, lean: Option[String])
