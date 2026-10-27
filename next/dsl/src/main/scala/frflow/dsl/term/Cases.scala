package frflow.dsl.term

import frflow.core.term.{Bound, Sym, When}
import scala.annotation.unused
import scala.deriving.Mirror

/** A match so far, `s.on[A](…).on[B](…)`: a term of its result, to which `on` adds an arm. Each arm is a host function
  * over its case (LNCS 7470 §3.2), so every interpreter binds the case's fields itself; Lean refuses a match that
  * misses a case, the evaluator gives `NoCase`.
  */
final class Cases[S, R](scrutinee: Term[S], arms: List[Branch[S, ?, R]])(using r: LeanType[R])
    extends Term[R]([T[_]] => (s: Sym[T]) => s.cases(scrutinee.run(s), arms.map(Cases.when(s, _)), r.ty)):
  inline def on[C <: S](using m: Mirror.ProductOf[C])(inline f: Cases.Fields[m.MirroredElemTypes, R]): Cases[S, R] =
    Cases(scrutinee, arms :+ Cases.branch[S, C, R](f))
  /** The arm of a case without fields, named by its value: `.on(Change.Clear)(result)`. */
  inline def on[C <: S & Singleton](@unused c: C)(using Mirror.ProductOf[C])(inline result: Term[R]): Cases[S, R] =
    Cases(scrutinee, arms :+ Cases.branch[S, C, R](result))

object Cases:
  /** The function an arm takes: of each of the case's fields (the result itself for a case without any). */
  type Fields[E <: Tuple, R] = E match
    case EmptyTuple                  => Term[R]
    case a *: EmptyTuple             => Term[a] => Term[R]
    case (a, b)                      => (Term[a], Term[b]) => Term[R]
    case (a, b, c)                   => (Term[a], Term[b], Term[c]) => Term[R]
    case (a, b, c, d)                => (Term[a], Term[b], Term[c], Term[d]) => Term[R]
    case (a, b, c, d, e)             => (Term[a], Term[b], Term[c], Term[d], Term[e]) => Term[R]

  inline def branch[S, C, R](inline f: Any): Branch[S, C, R] = ${ CaseMacros.branch[S, C, R]('f) }

  /** An arm as interpreter `s` takes it: the developer's function on `s`'s own variable for the case. */
  def when[T[_], S, C, R](s: Sym[T], b: Branch[S, C, R]): When[T, S, C, R] =
    When(b.c, Bound(b.hint, b.caseType.ty), Term.body(s, b.body)(using b.caseType))
