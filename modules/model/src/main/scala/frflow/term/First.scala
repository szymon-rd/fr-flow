package frflow
package term

import Cases.Fields

/** The first case of a match on an enum or a list, given its body (whose type is the match's):
  * `.on[Search.ById](id => …)`, `.on[Search.Everything.type](True)`, `.on[Nil.type](…)`.
  */
final class First[S, E <: Tuple] @scala.annotation.publicInBinary private[frflow] (scrutinee: Term[S], label: String):
  def apply[R](f: Fields[E, R]): Cases[S, R] = Cases(scrutinee, List(Term.namedCase(scrutinee, label, f.asInstanceOf[AnyRef])))
