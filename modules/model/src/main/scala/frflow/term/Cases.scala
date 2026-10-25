package frflow
package term

import scala.compiletime.constValue
import scala.deriving.Mirror

/** A match so far: a term of its result, to which `on` adds a case. Lean refuses one that misses a case. */
final class Cases[S, R] private[frflow] (scrutinee: Term[S], cases: List[Arm])
    extends Term[R](Tree.Match(scrutinee.termTree, cases), cases.head.tpe.asInstanceOf[LeanType[R]]):
  inline def on[C <: S](using m: Mirror.ProductOf[C]): On[S, m.MirroredElemTypes, R] = On(scrutinee, cases, constValue[m.MirroredLabel])

object Cases:
  /** The terms a case's lambda takes: one per field. */
  type Fields[T <: Tuple, R] = T match
    case EmptyTuple => Term[R]
    case a *: EmptyTuple => Term[a] => Term[R]
    case (a, b) => (Term[a], Term[b]) => Term[R]
    case (a, b, c) => (Term[a], Term[b], Term[c]) => Term[R]
    case (a, b, c, d) => (Term[a], Term[b], Term[c], Term[d]) => Term[R]
    case (a, b, c, d, e) => (Term[a], Term[b], Term[c], Term[d], Term[e]) => Term[R]
