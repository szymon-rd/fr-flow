package frflow.core.term

import frflow.core.name.DefName
import frflow.core.ty.Ty

/** A define's named body: its name, its type (`F` curried: `A => B => R`), and its lambda in final form (a `lam` per
  * input). What `Named.define` calls by name and `Functions.app` applies; the user's `Definition` made by `define`
  * carries it.
  */
final case class Body[F](name: DefName, ty: Ty, body: Final[F])
