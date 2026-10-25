package frflow

import frflow.types.Adt

private[frflow] enum Pat:
  /** A case class or an enum case, its fields bound (a wildcard binds none). */
  case Ctor(adt: Adt, ctor: frflow.types.Ctor, binders: List[Binder])
  case SomeP(b: Binder)
  /** `Except.error b` (`left`) or `Except.ok b`. */
  case InjP(left: Boolean, b: Binder)
  case NoneP
  case ConsP(h: Binder, t: Binder)
  case NilP
