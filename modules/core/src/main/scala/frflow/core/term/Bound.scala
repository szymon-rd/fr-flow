package frflow.core.term

import frflow.core.ty.Ty

/** What a binder needs besides its body: the name the developer gave it (a hint, for printing only) and its type. */
final case class Bound[A](hint: String, ty: Ty)
