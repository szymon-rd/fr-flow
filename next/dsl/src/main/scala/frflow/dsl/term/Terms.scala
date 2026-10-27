package frflow.dsl.term

import cats.syntax.all.*
import frflow.core.term.{Bound, Sym}

/** The binders of the term language, each a host function given each interpreter's own variable (`Term.body`): what
  * `TermSyntax`'s inline methods call once they have the parameters' names. A binder notes its variables' types (both
  * of `foldLeft`'s, `foldEither`'s and `pairwise`'s).
  */
object Terms:
  def forall[A: LeanType](hint: String, p: Term[A] => Term[Boolean]): Term[Boolean] =
    bound[A, Boolean]([T[_]] => (s: Sym[T]) => s.forall(Bound[A](hint, LeanType[A].ty))(Term.body(s, p)))

  /** `always[T](x => …)`: the rule over every value of `T` that can be made (owner §15). */
  def always[A: LeanType](hint: String, p: Term[A] => Term[Boolean]): Term[Boolean] =
    bound[A, Boolean]([T[_]] => (s: Sym[T]) => s.always(Bound[A](hint, LeanType[A].ty))(Term.body(s, p)))

  def exists[A: LeanType](hint: String, p: Term[A] => Term[Boolean]): Term[Boolean] =
    bound[A, Boolean]([T[_]] => (s: Sym[T]) => s.exists(Bound[A](hint, LeanType[A].ty))(Term.body(s, p)))

  /** An operation over a list's or an option's elements with a body (`all`, `map`, `optionAll`): one shape for each. */
  def over[C, A: LeanType, B, R: LeanType](xs: Term[C], hint: String, p: Term[A] => Term[B])(
      op: [T[_]] => Sym[T] => (T[C], Bound[A]) => (T[A] => T[B]) => T[R]): Term[R] =
    bound[A, R]([T[_]] => (s: Sym[T]) => op[T](s)(xs.run(s), Bound[A](hint, LeanType[A].ty))(Term.body(s, p)))

  def foldLeft[A: LeanType, B](xs: Term[List[A]], z: Term[B], hints: (String, String))(
      f: (Term[B], Term[A]) => Term[B]): Term[B] =
    given LeanType[B] = z.leanType
    both[A, B, B]([T[_]] => (s: Sym[T]) => s.foldLeft(xs.run(s), z.run(s), Bound[B](hints._1, z.leanType.ty),
      Bound[A](hints._2, LeanType[A].ty))((b, a) => f(Term.bound(s, b), Term.bound(s, a)).run(s)))

  def foldOption[A: LeanType, R](o: Term[Option[A]], ifNone: Term[R], hint: String)(ifSome: Term[A] => Term[R])
      : Term[R] =
    given LeanType[R] = ifNone.leanType
    bound[A, R]([T[_]] => (s: Sym[T]) =>
      s.foldOption(o.run(s), ifNone.run(s), Bound[A](hint, LeanType[A].ty))(Term.body(s, ifSome)))

  def foldEither[E: LeanType, A: LeanType, R: LeanType](v: Term[Either[E, A]], hints: (String, String))(
      l: Term[E] => Term[R], r: Term[A] => Term[R]): Term[R] =
    both[E, A, R]([T[_]] => (s: Sym[T]) => s.foldEither(v.run(s), Bound[E](hints._1, LeanType[E].ty),
      Bound[A](hints._2, LeanType[A].ty))(Term.body(s, l), Term.body(s, r)))

  def let[A, B: LeanType](v: Term[A], hint: String, body: Term[A] => Term[B]): Term[B] =
    given LeanType[A] = v.leanType
    bound[A, B]([T[_]] => (s: Sym[T]) => s.let(v.run(s), Bound[A](hint, LeanType[A].ty))(Term.body(s, body)))

  /** `xs.pairwise((a, b) => …)`: the body of every element with each later one. */
  def pairwise[A: LeanType](xs: Term[List[A]], hints: (String, String))(p: (Term[A], Term[A]) => Term[Boolean])
      : Term[Boolean] =
    bound[A, Boolean]([T[_]] => (s: Sym[T]) => s.pairwise(xs.run(s), Bound[A](hints._1, LeanType[A].ty),
      Bound[A](hints._2, LeanType[A].ty))((a, b) => p(Term.bound(s, a), Term.bound(s, b)).run(s)))

  /** A binder's term, noting its variable's type `A`. */
  private def bound[A: LeanType, R: LeanType](run: [T[_]] => Sym[T] => T[R]): Term[R] =
    Term.noted(Notes.of(LeanType[A].declares))(run)

  /** A binder of two variables' term, noting both types. */
  private def both[A: LeanType, B: LeanType, R: LeanType](run: [T[_]] => Sym[T] => T[R]): Term[R] =
    Term.noted(Notes.of(LeanType[A].declares |+| LeanType[B].declares))(run)
