package frflow.proof.obligation

import frflow.core.name.DefName
import frflow.core.ty.Ty

/** What a Definition stands for in a statement instead of itself: its proven code, its fixed value, or doing nothing
  * (for the root's `idle` try: `[]`, `none`, `False` or an input unchanged, by the Definition's type).
  */
enum Substitute:
  case Code(define: DefName)
  case Fixed(value: Constant)
  case Nothing

object Substitute:
  /** Whether a Definition of this type can do nothing: a function returning a proposition, a list, an option, or the
    * type of one of its inputs.
    */
  def canDoNothing(t: Ty): Boolean = t match
    case Ty.FnOf(ins, r) => r match
      case Ty.Bool | Ty.ListOf(_) | Ty.OptionOf(_) => true
      case other                                   => ins.contains(other)
    case _ => false
