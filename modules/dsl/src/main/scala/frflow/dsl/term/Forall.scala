package frflow.dsl.term

import frflow.core.term.Bound
import frflow.core.term.language.Sym

/** `forall((x: Term[A]) => …)`: the quantifier, its body kept as the host function it is, so a statement's leading
  * variables can be opened where the statement is closed (`node.Closing`, owner §41). As a term, the binder noting
  * its variable's type.
  */
final class Forall[A](val hint: String, val body: Term[A] => Term[Boolean])(using val bound: RocqType[A])
    extends Term[Boolean](Forall.of(hint, body)):
  /** Its body on a variable bound outside it. */
  def opened(x: Term[A]): Term[Boolean] = body(x)

object Forall:
  def of[A](hint: String, p: Term[A] => Term[Boolean])(using a: RocqType[A]): frflow.core.term.language.Final[Boolean] =
    [T[_]] => (s: Sym[T]) => s.noted(Notes.of(a.declares), s.forall(Bound[A](hint, a.ty))(Term.body(s, p)))
