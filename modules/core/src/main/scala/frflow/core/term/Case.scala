package frflow.core.term

import frflow.core.name.{CtorName, TypeName}
import frflow.core.ty.Ty

/** One case `C` of a sum type `S`, derived per case: its names, its fields' names and types (for the pattern Lean and
  * the IR bind), and `test`, the case when a value is it (a type test on `C`'s class, no cast).
  */
final case class Case[S, C](sum: TypeName, ctor: CtorName, fields: List[(String, Ty)], test: S => Option[C])
