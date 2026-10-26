package frflow.testing

import frflow.core.ty.Ty

/** A generator the tests used: the type it makes, and what the developer said of it (`describedAs`), if anything. */
final case class Made(ty: Ty, says: Option[String])
