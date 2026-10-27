package frflow
package term

import frflow.types.LeanType
import scala.deriving.Mirror
import scala.quoted.*

/** The case class `T` whose companion object has the singleton type `C`, with its fields' types `F`: found for any
  * case class, so that `Booking(r.room, r.start, r.end)` builds a term with no companion written for it.
  */
sealed trait CompanionOf[C]:
  type T
  type F <: Tuple

object CompanionOf:
  final class Of[C, T0, F0 <: Tuple] extends CompanionOf[C]:
    type T = T0
    type F = F0

  transparent inline given derived[C]: CompanionOf[C] = ${ of[C] }

  private[frflow] def of[C: Type](using q: Quotes): Expr[CompanionOf[C]] =
    import q.reflect.*
    val cls = TypeRepr.of[C].widen.typeSymbol.companionClass
    if cls == Symbol.noSymbol || !cls.flags.is(Flags.Case) || cls.declaredTypes.exists(_.isTypeParam) then
      report.errorAndAbort(s"${Type.show[C]} is not the companion of a case class")
    cls.typeRef.asType match
      case '[t] => Expr.summon[Mirror.ProductOf[t]] match
        case Some('{ $m: Mirror.ProductOf[t] { type MirroredElemTypes = f } }) =>
          Type.of[f] match
            case '[type f <: Tuple; f] => '{ Of[C, t, f]() }
        case _ => report.errorAndAbort(s"${cls.name} has no fields to build it from")

/** A case class built from terms with its own name: `Booking(r.room, r.start, r.end)` is a `Term[Booking]` (Scala tries
  * these when the case class's own `apply`, on values, does not fit the arguments).
  */
object Construct:
  import Tuple.Elem as E
  extension [C <: Singleton](companion: C)(using c: CompanionOf[C])
    def apply(a: Term[E[c.F, 0]])(using t: LeanType[c.T]): Term[c.T] = Term.make(t, List(a))
    def apply(a: Term[E[c.F, 0]], b: Term[E[c.F, 1]])(using t: LeanType[c.T]): Term[c.T] = Term.make(t, List(a, b))
    def apply(a: Term[E[c.F, 0]], b: Term[E[c.F, 1]], d: Term[E[c.F, 2]])(using t: LeanType[c.T]): Term[c.T] =
      Term.make(t, List(a, b, d))
    def apply(a: Term[E[c.F, 0]], b: Term[E[c.F, 1]], d: Term[E[c.F, 2]], e: Term[E[c.F, 3]])(using
        t: LeanType[c.T]): Term[c.T] = Term.make(t, List(a, b, d, e))
    def apply(a: Term[E[c.F, 0]], b: Term[E[c.F, 1]], d: Term[E[c.F, 2]], e: Term[E[c.F, 3]], f: Term[E[c.F, 4]])(using
        t: LeanType[c.T]): Term[c.T] = Term.make(t, List(a, b, d, e, f))
    def apply(a: Term[E[c.F, 0]], b: Term[E[c.F, 1]], d: Term[E[c.F, 2]], e: Term[E[c.F, 3]], f: Term[E[c.F, 4]],
        g: Term[E[c.F, 5]])(using t: LeanType[c.T]): Term[c.T] = Term.make(t, List(a, b, d, e, f, g))
