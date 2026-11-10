package frflow.dsl.lifted

import frflow.core.term.language.Sym
import frflow.dsl.term.{LeanType, Notes, Term, Terms, TermSyntax}

/** The term language's operations as the reader writes them (`Reader`): each binder's variable named as the Scala
  * named it, each operation one of `TermSyntax`'s, so lifted code and a model's own terms are the same terms.
  */
object LiftOps:
  def all[A: LeanType](xs: Term[List[A]], hint: String)(p: Term[A] => Term[Boolean]): Term[Boolean] =
    Terms.over(xs, hint, p)([T[_]] => (s: Sym[T]) => s.all[A])
  def any[A: LeanType](xs: Term[List[A]], hint: String)(p: Term[A] => Term[Boolean]): Term[Boolean] =
    Terms.over(xs, hint, p)([T[_]] => (s: Sym[T]) => s.any[A])
  def filter[A: LeanType](xs: Term[List[A]], hint: String)(p: Term[A] => Term[Boolean]): Term[List[A]] =
    Terms.over(xs, hint, p)([T[_]] => (s: Sym[T]) => s.filter[A])(using LeanType[A], xs.leanType)
  def find[A: LeanType](xs: Term[List[A]], hint: String)(p: Term[A] => Term[Boolean]): Term[Option[A]] =
    Terms.over(xs, hint, p)([T[_]] => (s: Sym[T]) => s.find[A])
  def map[A: LeanType, B: LeanType](xs: Term[List[A]], hint: String)(f: Term[A] => Term[B]): Term[List[B]] =
    Terms.over(xs, hint, f)([T[_]] => (s: Sym[T]) => s.map[A, B])
  def flatMap[A: LeanType, B: LeanType](xs: Term[List[A]], hint: String)(f: Term[A] => Term[List[B]])
      : Term[List[B]] = Terms.over(xs, hint, f)([T[_]] => (s: Sym[T]) => s.flatMap[A, B])
  def nil[A](using a: LeanType[A]): Term[List[A]] =
    Term.noted(Notes.of(a.declares))([T[_]] => (s: Sym[T]) => s.nil[A](a.ty))
  def contains[A](xs: Term[List[A]], x: Term[A]): Term[Boolean] = TermSyntax.contains(xs)(x)
  def isEmpty[A](xs: Term[List[A]]): Term[Boolean] = TermSyntax.isEmpty(xs)

  def optionAll[A: LeanType](o: Term[Option[A]], hint: String)(p: Term[A] => Term[Boolean]): Term[Boolean] =
    Terms.over(o, hint, p)([T[_]] => (s: Sym[T]) => s.optionAll[A])
  def optionAny[A: LeanType](o: Term[Option[A]], hint: String)(p: Term[A] => Term[Boolean]): Term[Boolean] =
    Terms.over(o, hint, p)([T[_]] => (s: Sym[T]) => s.optionAny[A])
  def optionMap[A: LeanType, B: LeanType](o: Term[Option[A]], hint: String)(f: Term[A] => Term[B]): Term[Option[B]] =
    Terms.foldOption(o, TermSyntax.none[B], hint)(a => TermSyntax.some(f(a)))
  def optionContains[A: LeanType](o: Term[Option[A]], x: Term[A]): Term[Boolean] =
    Terms.foldOption(o, TermSyntax.False, "a")(a => TermSyntax.===(a)(x))
  def isNone[A: LeanType](o: Term[Option[A]]): Term[Boolean] = Terms.foldOption(o, TermSyntax.True, "a")(_ =>
    TermSyntax.False)

  def pair[A, B](a: Term[A], b: Term[B])(using LeanType[(A, B)]): Term[(A, B)] =
    Term.both(a, b)([T[_]] => (s: Sym[T]) => s.pair[A, B])
  def hasKey[K, V: LeanType](m: Term[Map[K, V]], k: Term[K]): Term[Boolean] =
    TermSyntax.isDefined(TermSyntax.get(m)(k))
  def member[A](set: Term[Set[A]], x: Term[A]): Term[Boolean] =
    Term.both(set, x)([T[_]] => (s: Sym[T]) => s.member[A])

  /** A case of a sum as a value of the sum (`Shape.Circle` where a `Shape` is used): the same term. */
  def widened[C, S: LeanType](t: Term[C]): Term[S] =
    Term([T[_]] => (s: Sym[T]) => t.run(s).asInstanceOf[T[S]]) // a case's term is its sum's in every interpreter

  def cons[A](x: Term[A], xs: Term[List[A]]): Term[List[A]] = TermSyntax.::(xs)(x)
  def orElse[A](o: Term[Option[A]], default: Term[A]): Term[A] =
    Term.both(o, default)([T[_]] => (s: Sym[T]) => s.getOrElse[A])(using default.leanType)
  def valueOr[K, V](m: Term[Map[K, V]], k: Term[K], default: Term[V]): Term[V] =
    Term([T[_]] => (s: Sym[T]) => s.getOrElseAt(m.run(s), k.run(s), default.run(s)))(using default.leanType)
  def put[K, V](m: Term[Map[K, V]], k: Term[K], v: Term[V]): Term[Map[K, V]] =
    Term([T[_]] => (s: Sym[T]) => s.updated(m.run(s), k.run(s), v.run(s)))(using m.leanType)
