package frflow.dsl.term

import frflow.core.expr.Value
import frflow.core.term.Sym

/** A value as a constant term: what the DSL's implicit conversions (`Term.value`, `Term.int`) make, noting its type;
  * a value that is not data is noted as a fault on the term, which fails its node.
  */
object Lift:
  def constant[A](a: A)(using t: LeanType[A]): Term[A] = Reify(t, a) match
    case Right(v) => Term.noted(Notes.of(t.declares))([T[_]] => (s: Sym[T]) => s.lit(a, v, t.ty))
    case Left(f)  => Term.noted(Notes.fault(f))([T[_]] => (s: Sym[T]) => s.lit(a, Value.Unit, t.ty))
