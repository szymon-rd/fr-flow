package frflow.dsl.term

import frflow.core.term.{Selector, Sym}
import frflow.dsl.build.Source
import scala.annotation.targetName
import scala.deriving.Mirror

/** The operations of the term language as models write them, each one operation of `core.term`'s algebras on the
  * operands' terms (`Term.one`, `Term.both`, the binders of `Terms`). Bodies are host functions (higher-order abstract
  * syntax); their parameters' names are read at compile time, for printing only. `implies` is alphanumeric, so it
  * binds last: `a && b implies c` is `(a && b) implies c`, as it reads; a chain of them needs its parentheses
  * (`Implication`).
  */
object TermSyntax:
  extension [A](a: Term[A])
    def ===(b: Term[A]): Term[Boolean] = Term.both(a, b)([T[_]] => (s: Sym[T]) => s.eq[A])
    def =!=(b: Term[A]): Term[Boolean] = !(a === b)
    /** `x :: xs`: Scala reads a right-associative extension with its left operand as the receiver. */
    def ::(xs: Term[List[A]]): Term[List[A]] = Term.both(a, xs)([T[_]] => (s: Sym[T]) => s.cons[A])(using xs.leanType)
    /** `b.updated(_.start, t)`: the record with one field replaced, the field checked at compile time. */
    inline def updated[F](inline field: Term[A] => Term[F], v: Term[F]): Term[A] =
      ${ CaseMacros.updated[A, F]('a, 'field, 'v) }
    /** `s.on[Case](fields => …).on[Other](…)`: a match, one arm per case, each named by its case's type; a case
      * without fields by its singleton type, in any position: `.on[Change.Clear.type](result)`.
      */
    inline def on[C <: A](using m: Mirror.ProductOf[C])[R](inline f: Cases.Fields[m.MirroredElemTypes, R])(
        using LeanType[R]): Cases[A, R] = Cases(a, List(Cases.branch[A, C, R](f)))
  extension (a: Term[Boolean])
    def &&(b: Term[Boolean]): Term[Boolean] = Term.both(a, b)([T[_]] => (s: Sym[T]) => s.and)
    def ||(b: Term[Boolean]): Term[Boolean] = Term.both(a, b)([T[_]] => (s: Sym[T]) => s.or)
    def unary_! : Term[Boolean] = Term.one(a)([T[_]] => (s: Sym[T]) => s.not)
  extension (inline a: Term[Boolean])
    /** Refused at compile time as the left operand of another `implies` unless in parentheses (`Implication`). */
    inline infix def implies(inline b: Term[Boolean]): Term[Boolean] = ${ Implication.checked('a, 'b) }
  extension (a: Term[BigInt])
    def +(b: Term[BigInt]): Term[BigInt] = Term.both(a, b)([T[_]] => (s: Sym[T]) => s.add)
    def -(b: Term[BigInt]): Term[BigInt] = Term.both(a, b)([T[_]] => (s: Sym[T]) => s.sub)
    def <(b: Term[BigInt]): Term[Boolean] = Term.both(a, b)([T[_]] => (s: Sym[T]) => s.lt)
    def <=(b: Term[BigInt]): Term[Boolean] = Term.both(a, b)([T[_]] => (s: Sym[T]) => s.le)
    def >(b: Term[BigInt]): Term[Boolean] = b < a
    def >=(b: Term[BigInt]): Term[Boolean] = b <= a
  extension [A](xs: Term[List[A]])
    def length: Term[BigInt] = Term.one(xs)([T[_]] => (s: Sym[T]) => s.length[A])
    /** Lean's `List.Nodup`: no element twice. */
    def allDistinct: Term[Boolean] = Term.one(xs)([T[_]] => (s: Sym[T]) => s.nodup[A])
    def ++(ys: Term[List[A]]): Term[List[A]] =
      Term.both(xs, ys)([T[_]] => (s: Sym[T]) => s.append[A])(using xs.leanType)
    /** `xs :+ x`: `x` at the end (Lean's `xs ++ [x]`). */
    def :+(x: Term[A]): Term[List[A]] =
      xs ++ (x :: Term[List[A]]([T[_]] => (s: Sym[T]) => s.nil[A](x.leanType.ty))(using xs.leanType))
    def contains(x: Term[A]): Term[Boolean] = Term.both(xs, x)([T[_]] => (s: Sym[T]) => s.contains[A])
    def isEmpty: Term[Boolean] = Term.one(xs)([T[_]] => (s: Sym[T]) => s.isEmpty[A])
  extension [A: LeanType](xs: Term[List[A]])
    inline def forall(inline p: Term[A] => Term[Boolean]): Term[Boolean] =
      Terms.over(xs, hint(Source.of(p).params), p)([T[_]] => (s: Sym[T]) => s.all[A])
    inline def exists(inline p: Term[A] => Term[Boolean]): Term[Boolean] =
      Terms.over(xs, hint(Source.of(p).params), p)([T[_]] => (s: Sym[T]) => s.any[A])
    inline def filter(inline p: Term[A] => Term[Boolean]): Term[List[A]] =
      Terms.over(xs, hint(Source.of(p).params), p)([T[_]] => (s: Sym[T]) => s.filter[A])(using LeanType[A], xs.leanType)
    inline def foldLeft[B](z: Term[B])(inline f: (Term[B], Term[A]) => Term[B]): Term[B] =
      Terms.foldLeft(xs, z, hints(Source.of(f).params))(f)
    inline def map[B: LeanType](inline f: Term[A] => Term[B]): Term[List[B]] =
      Terms.over(xs, hint(Source.of(f).params), f)([T[_]] => (s: Sym[T]) => s.map[A, B])
    inline def flatMap[B: LeanType](inline f: Term[A] => Term[List[B]]): Term[List[B]] =
      Terms.over(xs, hint(Source.of(f).params), f)([T[_]] => (s: Sym[T]) => s.flatMap[A, B])
    /** The first element meeting `p`, if any (Lean's `List.find?`). */
    inline def find(inline p: Term[A] => Term[Boolean]): Term[Option[A]] =
      Terms.over(xs, hint(Source.of(p).params), p)([T[_]] => (s: Sym[T]) => s.find[A])
    def zip[B: LeanType](ys: Term[List[B]]): Term[List[(A, B)]] =
      Term.both(xs, ys)([T[_]] => (s: Sym[T]) => s.zip[A, B])
    /** Lean's `List.Pairwise`: `p` of every element with each later one (`xs.pairwise(apart)`, or a lambda). */
    inline def pairwise(inline p: (Term[A], Term[A]) => Term[Boolean]): Term[Boolean] =
      Terms.pairwise(xs, Source.of(p).params match
        case List(a, b) => (a, b)
        case _          => ("a", "b"))(p)
  extension [A: LeanType](o: Term[Option[A]])
    inline def fold[R](ifNone: Term[R])(inline ifSome: Term[A] => Term[R]): Term[R] =
      Terms.foldOption(o, ifNone, hint(Source.of(ifSome).params))(ifSome)
    /** None, or one meeting `p` (Scala's `o.forall`). */
    @targetName("optionForall") inline def forall(inline p: Term[A] => Term[Boolean]): Term[Boolean] =
      Terms.over(o, hint(Source.of(p).params), p)([T[_]] => (s: Sym[T]) => s.optionAll[A])
    /** One meeting `p` (Scala's `o.exists`). */
    @targetName("optionExists") inline def exists(inline p: Term[A] => Term[Boolean]): Term[Boolean] =
      Terms.over(o, hint(Source.of(p).params), p)([T[_]] => (s: Sym[T]) => s.optionAny[A])
    def getOrElse(default: Term[A]): Term[A] = Term.both(o, default)([T[_]] => (s: Sym[T]) => s.getOrElse[A])
  extension [A](o: Term[Option[A]])
    def isDefined: Term[Boolean] = Term.one(o)([T[_]] => (s: Sym[T]) => s.isDefined[A])
  extension [E: LeanType, A: LeanType](v: Term[Either[E, A]])
    inline def fold[R: LeanType](inline onLeft: Term[E] => Term[R], inline onRight: Term[A] => Term[R]): Term[R] =
      Terms.foldEither(v, (hint(Source.of(onLeft).params), hint(Source.of(onRight).params)))(onLeft, onRight)
    def isRight: Term[Boolean] = Terms.foldEither(v, ("e", "a"))(_ => False, _ => True)
    def isLeft: Term[Boolean] = Terms.foldEither(v, ("e", "a"))(_ => True, _ => False)
  extension [K, V: LeanType](m: Term[Map[K, V]])
    /** The value at `k`, if any. */
    def get(k: Term[K]): Term[Option[V]] = Term.both(m, k)([T[_]] => (s: Sym[T]) => s.get[K, V])
    def getOrElse(k: Term[K], default: Term[V]): Term[V] =
      Term([T[_]] => (s: Sym[T]) => s.getOrElseAt(m.run(s), k.run(s), default.run(s)))
  extension [K, V](m: Term[Map[K, V]])
    def updated(k: Term[K], v: Term[V]): Term[Map[K, V]] =
      Term([T[_]] => (s: Sym[T]) => s.updated(m.run(s), k.run(s), v.run(s)))(using m.leanType)
  extension [A](set: Term[Set[A]])
    @targetName("setContains") def contains(x: Term[A]): Term[Boolean] =
      Term.both(set, x)([T[_]] => (s: Sym[T]) => s.member[A])
    def incl(x: Term[A]): Term[Set[A]] = Term.both(set, x)([T[_]] => (s: Sym[T]) => s.incl[A])(using set.leanType)
    def union(other: Term[Set[A]]): Term[Set[A]] =
      Term.both(set, other)([T[_]] => (s: Sym[T]) => s.union[A])(using set.leanType)
  extension [A, B](p: Term[(A, B)])
    def _1(using a: LeanType[A]): Term[A] = Term.one(p)([T[_]] => (s: Sym[T]) => s.field(_, Selector.first[A, B](a.ty)))
    def _2(using b: LeanType[B]): Term[B] =
      Term.one(p)([T[_]] => (s: Sym[T]) => s.field(_, Selector.second[A, B](b.ty)))

  /** The Boolean constants: a Scala `Boolean` is not made a term implicitly, so `x === true` cannot be mistaken. */
  val True: Term[Boolean] = Term([T[_]] => (s: Sym[T]) => s.bool(true))
  val False: Term[Boolean] = Term([T[_]] => (s: Sym[T]) => s.bool(false))

  inline def forall[A: LeanType](inline p: Term[A] => Term[Boolean]): Term[Boolean] =
    Terms.forall(hint(Source.of(p).params), p)
  inline def forall[A: LeanType, B: LeanType](inline p: (Term[A], Term[B]) => Term[Boolean]): Term[Boolean] =
    val (a, b) = hints(Source.of(p).params)
    Terms.forall[A](a, x => Terms.forall[B](b, y => p(x, y)))
  inline def forall[A: LeanType, B: LeanType, C: LeanType](inline p: (Term[A], Term[B], Term[C]) => Term[Boolean])
      : Term[Boolean] =
    val h = names(Source.of(p).params, 3)
    Terms.forall[A](h(0), x => Terms.forall[B](h(1), y => Terms.forall[C](h(2), z => p(x, y, z))))
  inline def forall[A: LeanType, B: LeanType, C: LeanType, D: LeanType](
      inline p: (Term[A], Term[B], Term[C], Term[D]) => Term[Boolean]): Term[Boolean] =
    val h = names(Source.of(p).params, 4)
    Terms.forall[A](h(0), w => Terms.forall[B](h(1), x =>
      Terms.forall[C](h(2), y => Terms.forall[D](h(3), z => p(w, x, y, z)))))
  inline def forall[A: LeanType, B: LeanType, C: LeanType, D: LeanType, E: LeanType](
      inline p: (Term[A], Term[B], Term[C], Term[D], Term[E]) => Term[Boolean]): Term[Boolean] =
    val h = names(Source.of(p).params, 5)
    Terms.forall[A](h(0), v => Terms.forall[B](h(1), w => Terms.forall[C](h(2), x =>
      Terms.forall[D](h(3), y => Terms.forall[E](h(4), z => p(v, w, x, y, z))))))
  inline def forall[A: LeanType, B: LeanType, C: LeanType, D: LeanType, E: LeanType, G: LeanType](
      inline p: (Term[A], Term[B], Term[C], Term[D], Term[E], Term[G]) => Term[Boolean]): Term[Boolean] =
    val h = names(Source.of(p).params, 6)
    Terms.forall[A](h(0), u => Terms.forall[B](h(1), v => Terms.forall[C](h(2), w =>
      Terms.forall[D](h(3), x => Terms.forall[E](h(4), y => Terms.forall[G](h(5), z => p(u, v, w, x, y, z)))))))
  /** `when(free)(held :+ request).otherwise(held)`: the conditional, each branch named where it is written. */
  def when[A](condition: Term[Boolean])(ifTrue: Term[A]): Conditional[A] = Conditional(condition, ifTrue)
  /** `let(v)(x => body)`: `v` named for the body, computed once (Lean's `let`). */
  inline def let[A, B: LeanType](v: Term[A])(inline body: Term[A] => Term[B]): Term[B] =
    Terms.let(v, hint(Source.of(body).params), body)
  /** `make[Booking](room, start, end)`: a value of a case class or an enum's case from its fields' terms. */
  transparent inline def make[R](inline args: Term[?]*): Term[?] = ${ CaseMacros.make[R]('args) }

  def some[A](a: Term[A]): Term[Option[A]] =
    Term.one(a)([T[_]] => (s: Sym[T]) => s.some[A])(using LeanType.option(using a.leanType))
  def none[A](using a: LeanType[A]): Term[Option[A]] =
    Term.noted(Notes.of(a.declares))([T[_]] => (s: Sym[T]) => s.none[A](a.ty))
  def left[E, A](e: Term[E])(using t: LeanType[Either[E, A]]): Term[Either[E, A]] =
    Term.one(e)([T[_]] => (s: Sym[T]) => (x: T[E]) => s.left[E, A](x, t.ty))
  def right[E, A](a: Term[A])(using t: LeanType[Either[E, A]]): Term[Either[E, A]] =
    Term.one(a)([T[_]] => (s: Sym[T]) => (x: T[A]) => s.right[E, A](x, t.ty))

  private def hint(names: List[String]): String = names.headOption.getOrElse("x")
  private def hints(names: List[String]): (String, String) = (hint(names), hint(names.drop(1)))
  private def names(ns: List[String], n: Int): Vector[String] = ns.padTo(n, "x").toVector
