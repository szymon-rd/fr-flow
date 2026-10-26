package frflow.core.expr

import frflow.core.name.{CtorName, TypeName}

/** What one arm of a match takes apart. */
enum Pattern:
  /** A case class or an enum case, its fields bound in order. */
  case Ctor(ty: TypeName, ctor: CtorName, fields: List[Binder])
  case SomeP(x: Binder)
  case NoneP
  case Outcome(side: Side, x: Binder)
  case ConsP(head: Binder, tail: Binder)
  case NilP

  def binders: List[Binder] = this match
    case Ctor(_, _, bs)  => bs
    case SomeP(x)        => List(x)
    case Outcome(_, x)   => List(x)
    case ConsP(h, t)     => List(h, t)
    case NoneP | NilP    => Nil
