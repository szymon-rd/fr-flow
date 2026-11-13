package frflow.dsl.term

import cats.syntax.all.*
import frflow.core.term.Bound
import frflow.core.term.language.Sym

/** The binders of the term language, each a host function given each interpreter's own variable (`Term.body`): what
  * `TermSyntax`'s inline methods call once they have the parameters' names. A binder notes its variables' types (both
  * of `foldLeft`'s, `foldEither`'s and `pairwise`'s).
  */
object Terms:
  /** A `forall`, keeping its body as written, so a statement can open it (`Forall`). */
  def forall[A: RocqType](hint: String, p: Term[A] => Term[Boolean]): Term[Boolean] = Forall(hint, p)

  /** `always[T](x => …)`: the rule over every value of `T` that can be made (owner §15). */
  def always[A: RocqType](hint: String, p: Term[A] => Term[Boolean]): Term[Boolean] =
    bound[A, Boolean]([T[_]] => (s: Sym[T]) => s.always(Bound[A](hint, RocqType[A].ty))(Term.body(s, p)))

  /** `exists(x => …)`: some value of `A` meets the body (not opened where a statement is closed: it is no premise). */
  def exists[A: RocqType](hint: String, p: Term[A] => Term[Boolean]): Term[Boolean] =
    bound[A, Boolean]([T[_]] => (s: Sym[T]) => s.exists(Bound[A](hint, RocqType[A].ty))(Term.body(s, p)))

  /** An operation over a list's or an option's elements with a body (`all`, `map`, `optionAll`): one shape for each. */
  def over[C, A: RocqType, B, R: RocqType](xs: Term[C], hint: String, p: Term[A] => Term[B])(
      op: [T[_]] => Sym[T] => (T[C], Bound[A]) => (T[A] => T[B]) => T[R]): Term[R] =
    bound[A, R]([T[_]] => (s: Sym[T]) => op[T](s)(xs.run(s), Bound[A](hint, RocqType[A].ty))(Term.body(s, p)))

  def foldLeft[A: RocqType, B](xs: Term[List[A]], z: Term[B], hints: (String, String))(
      f: (Term[B], Term[A]) => Term[B]): Term[B] =
    given RocqType[B] = z.rocqType
    both[A, B, B]([T[_]] => (s: Sym[T]) => s.foldLeft(xs.run(s), z.run(s), Bound[B](hints._1, z.rocqType.ty),
      Bound[A](hints._2, RocqType[A].ty))((b, a) => f(Term.bound(s, b), Term.bound(s, a)).run(s)))

  def foldOption[A: RocqType, R](o: Term[Option[A]], ifNone: Term[R], hint: String)(ifSome: Term[A] => Term[R])
      : Term[R] =
    given RocqType[R] = ifNone.rocqType
    bound[A, R]([T[_]] => (s: Sym[T]) =>
      s.foldOption(o.run(s), ifNone.run(s), Bound[A](hint, RocqType[A].ty))(Term.body(s, ifSome)))

  def foldEither[E: RocqType, A: RocqType, R: RocqType](v: Term[Either[E, A]], hints: (String, String))(
      l: Term[E] => Term[R], r: Term[A] => Term[R]): Term[R] =
    both[E, A, R]([T[_]] => (s: Sym[T]) => s.foldEither(v.run(s), Bound[E](hints._1, RocqType[E].ty),
      Bound[A](hints._2, RocqType[A].ty))(Term.body(s, l), Term.body(s, r)))

  def let[A, B: RocqType](v: Term[A], hint: String, body: Term[A] => Term[B]): Term[B] =
    given RocqType[A] = v.rocqType
    bound[A, B]([T[_]] => (s: Sym[T]) => s.let(v.run(s), Bound[A](hint, RocqType[A].ty))(Term.body(s, body)))

  /** `xs.pairwise((a, b) => …)`: the body of every element with each later one. */
  def pairwise[A: RocqType](xs: Term[List[A]], hints: (String, String))(p: (Term[A], Term[A]) => Term[Boolean])
      : Term[Boolean] =
    bound[A, Boolean]([T[_]] => (s: Sym[T]) => s.pairwise(xs.run(s), Bound[A](hints._1, RocqType[A].ty),
      Bound[A](hints._2, RocqType[A].ty))((a, b) => p(Term.bound(s, a), Term.bound(s, b)).run(s)))

  /** A binder's term, noting its variable's type `A`. */
  private def bound[A: RocqType, R: RocqType](run: [T[_]] => Sym[T] => T[R]): Term[R] =
    Term.noted(Notes.of(RocqType[A].declares))(run)

  /** A binder of two variables' term, noting both types. */
  private def both[A: RocqType, B: RocqType, R: RocqType](run: [T[_]] => Sym[T] => T[R]): Term[R] =
    Term.noted(Notes.of(RocqType[A].declares |+| RocqType[B].declares))(run)
