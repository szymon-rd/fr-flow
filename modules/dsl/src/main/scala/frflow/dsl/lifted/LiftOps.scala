package frflow.dsl.lifted

import frflow.core.term.language.Sym
import frflow.dsl.term.{RocqType, Notes, Term, Terms, TermSyntax}

/** The term language's operations as the class compiler writes them (`compiled`): each binder's variable named as
  * the Scala named it, each operation one of `TermSyntax`'s, so lifted code and a model's own terms are the same
  * terms.
  */
object LiftOps:
  def all[A: RocqType](xs: Term[List[A]], hint: String)(p: Term[A] => Term[Boolean]): Term[Boolean] =
    Terms.over(xs, hint, p)([T[_]] => (s: Sym[T]) => s.all[A])
  def any[A: RocqType](xs: Term[List[A]], hint: String)(p: Term[A] => Term[Boolean]): Term[Boolean] =
    Terms.over(xs, hint, p)([T[_]] => (s: Sym[T]) => s.any[A])
  def filter[A: RocqType](xs: Term[List[A]], hint: String)(p: Term[A] => Term[Boolean]): Term[List[A]] =
    Terms.over(xs, hint, p)([T[_]] => (s: Sym[T]) => s.filter[A])(using RocqType[A], xs.rocqType)
  def find[A: RocqType](xs: Term[List[A]], hint: String)(p: Term[A] => Term[Boolean]): Term[Option[A]] =
    Terms.over(xs, hint, p)([T[_]] => (s: Sym[T]) => s.find[A])
  def map[A: RocqType, B: RocqType](xs: Term[List[A]], hint: String)(f: Term[A] => Term[B]): Term[List[B]] =
    Terms.over(xs, hint, f)([T[_]] => (s: Sym[T]) => s.map[A, B])
  def flatMap[A: RocqType, B: RocqType](xs: Term[List[A]], hint: String)(f: Term[A] => Term[List[B]])
      : Term[List[B]] = Terms.over(xs, hint, f)([T[_]] => (s: Sym[T]) => s.flatMap[A, B])
  def nil[A](using a: RocqType[A]): Term[List[A]] =
    Term.noted(Notes.of(a.declares))([T[_]] => (s: Sym[T]) => s.nil[A](a.ty))
  def contains[A](xs: Term[List[A]], x: Term[A]): Term[Boolean] = TermSyntax.contains(xs)(x)
  def isEmpty[A](xs: Term[List[A]]): Term[Boolean] = TermSyntax.isEmpty(xs)

  def optionAll[A: RocqType](o: Term[Option[A]], hint: String)(p: Term[A] => Term[Boolean]): Term[Boolean] =
    Terms.over(o, hint, p)([T[_]] => (s: Sym[T]) => s.optionAll[A])
  def optionAny[A: RocqType](o: Term[Option[A]], hint: String)(p: Term[A] => Term[Boolean]): Term[Boolean] =
    Terms.over(o, hint, p)([T[_]] => (s: Sym[T]) => s.optionAny[A])
  def optionMap[A: RocqType, B: RocqType](o: Term[Option[A]], hint: String)(f: Term[A] => Term[B]): Term[Option[B]] =
    Terms.foldOption(o, TermSyntax.none[B], hint)(a => TermSyntax.some(f(a)))
  def optionContains[A: RocqType](o: Term[Option[A]], x: Term[A]): Term[Boolean] =
    Terms.foldOption(o, TermSyntax.False, "a")(a => TermSyntax.===(a)(x))
  def isNone[A: RocqType](o: Term[Option[A]]): Term[Boolean] = Terms.foldOption(o, TermSyntax.True, "a")(_ =>
    TermSyntax.False)

  def pair[A, B](a: Term[A], b: Term[B])(using RocqType[(A, B)]): Term[(A, B)] =
    Term.both(a, b)([T[_]] => (s: Sym[T]) => s.pair[A, B])
  def hasKey[K, V: RocqType](m: Term[Map[K, V]], k: Term[K]): Term[Boolean] =
    TermSyntax.isDefined(TermSyntax.get(m)(k))
  def member[A](set: Term[Set[A]], x: Term[A]): Term[Boolean] =
    Term.both(set, x)([T[_]] => (s: Sym[T]) => s.member[A])

  /** A case of a sum as a value of the sum (`Shape.Circle` where a `Shape` is used): the same term. */
  def widened[C, S: RocqType](t: Term[C]): Term[S] =
    Term([T[_]] => (s: Sym[T]) => t.run(s).asInstanceOf[T[S]]) // a case's term is its sum's in every interpreter

  def cons[A](x: Term[A], xs: Term[List[A]]): Term[List[A]] = TermSyntax.::(xs)(x)
  def orElse[A](o: Term[Option[A]], default: Term[A]): Term[A] =
    Term.both(o, default)([T[_]] => (s: Sym[T]) => s.getOrElse[A])(using default.rocqType)
  def valueOr[K, V](m: Term[Map[K, V]], k: Term[K], default: Term[V]): Term[V] =
    Term([T[_]] => (s: Sym[T]) => s.getOrElseAt(m.run(s), k.run(s), default.run(s)))(using default.rocqType)
  def put[K, V](m: Term[Map[K, V]], k: Term[K], v: Term[V]): Term[Map[K, V]] =
    Term([T[_]] => (s: Sym[T]) => s.updated(m.run(s), k.run(s), v.run(s)))(using m.rocqType)
