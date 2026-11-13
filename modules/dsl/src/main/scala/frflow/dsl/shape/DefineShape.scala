package frflow.dsl.shape

import frflow.core.code.Code
import frflow.core.expr.{Binder, Lambda}
import frflow.core.name.{DefName, VarId}
import frflow.core.spec.Written
import frflow.core.term.Bound
import frflow.core.term.language.{Body, Sym}
import frflow.dsl.build.Deferred
import frflow.dsl.term.{RocqType, Term}
import frflow.dsl.vocab.{Definition, OnTheSpot, Spot}

/** The shape of a define of type `F`: its lambda over its inputs' terms, the body on the inputs' variables (bound at
  * levels `0 … n-1` outside it: the written lambda, printed as its `def`), and the Definition it makes, carrying its
  * body, the same lambda in final form, one `lam` per input (LNCS 7470 §3.2), each interpreter giving its own
  * variables. One instance per arity.
  */
trait DefineShape[F]:
  type Lam <: AnyRef
  def types: List[RocqType[?]]
  def rocqType: RocqType[F]
  def body(f: Lam, hints: List[String]): (List[Binder], Term[?])
  def made(name: DefName, f: Lam, hints: List[String], lambda: Deferred[Written[Lambda]]): Definition[F]

object DefineShape:
  given one[A, R](using a: RocqType[A], r: RocqType[R]): DefineShape[A => R] with
    type Lam = Term[A] => Term[R]
    val types: List[RocqType[?]] = List(a)
    def rocqType: RocqType[A => R] = RocqType[A => R]
    def body(f: Lam, hints: List[String]): (List[Binder], Term[?]) =
      val x = binder(0, a, hints)
      (List(x), f(Term.free(x)))
    def made(name: DefName, f: Lam, hints: List[String], lambda: Deferred[Written[Lambda]]): Definition[A => R] =
      spot(name, lambda, Body(name, RocqType[A => R].ty,
        [T[_]] => (s: Sym[T]) => s.lam(bound(0, a, hints))(Term.body(s, f))))

  given two[A, B, R](using a: RocqType[A], b: RocqType[B], r: RocqType[R]): DefineShape[(A, B) => R] with
    type Lam = (Term[A], Term[B]) => Term[R]
    val types: List[RocqType[?]] = List(a, b)
    def rocqType: RocqType[(A, B) => R] = RocqType[(A, B) => R]
    def body(f: Lam, hints: List[String]): (List[Binder], Term[?]) =
      val (x, y) = (binder(0, a, hints), binder(1, b, hints))
      (List(x, y), f(Term.free(x), Term.free(y)))
    def made(name: DefName, f: Lam, hints: List[String], lambda: Deferred[Written[Lambda]])
        : Definition[(A, B) => R] =
      spot(name, lambda, Body(name, RocqType[A => B => R].ty, [T[_]] => (s: Sym[T]) =>
        s.lam(bound(0, a, hints))(x => s.lam(bound(1, b, hints))(y => f(Term.bound(s, x), Term.bound(s, y)).run(s)))))
  given three[A, B, C, R](using a: RocqType[A], b: RocqType[B], c: RocqType[C], r: RocqType[R])
      : DefineShape[(A, B, C) => R] with
    type Lam = (Term[A], Term[B], Term[C]) => Term[R]
    val types: List[RocqType[?]] = List(a, b, c)
    def rocqType: RocqType[(A, B, C) => R] = RocqType[(A, B, C) => R]
    def body(f: Lam, hints: List[String]): (List[Binder], Term[?]) =
      val (x, y, z) = (binder(0, a, hints), binder(1, b, hints), binder(2, c, hints))
      (List(x, y, z), f(Term.free(x), Term.free(y), Term.free(z)))
    def made(name: DefName, f: Lam, hints: List[String], lambda: Deferred[Written[Lambda]])
        : Definition[(A, B, C) => R] =
      spot(name, lambda, Body(name, RocqType[A => B => C => R].ty, [T[_]] => (s: Sym[T]) =>
        s.lam(bound(0, a, hints))(x => s.lam(bound(1, b, hints))(y => s.lam(bound(2, c, hints))(z =>
          f(Term.bound(s, x), Term.bound(s, y), Term.bound(s, z)).run(s))))))

  given four[A, B, C, D, R](using a: RocqType[A], b: RocqType[B], c: RocqType[C], d: RocqType[D], r: RocqType[R])
      : DefineShape[(A, B, C, D) => R] with
    type Lam = (Term[A], Term[B], Term[C], Term[D]) => Term[R]
    val types: List[RocqType[?]] = List(a, b, c, d)
    def rocqType: RocqType[(A, B, C, D) => R] = RocqType[(A, B, C, D) => R]
    def body(f: Lam, hints: List[String]): (List[Binder], Term[?]) =
      val (w, x, y, z) = (binder(0, a, hints), binder(1, b, hints), binder(2, c, hints), binder(3, d, hints))
      (List(w, x, y, z), f(Term.free(w), Term.free(x), Term.free(y), Term.free(z)))
    def made(name: DefName, f: Lam, hints: List[String], lambda: Deferred[Written[Lambda]])
        : Definition[(A, B, C, D) => R] =
      spot(name, lambda, Body(name, RocqType[A => B => C => D => R].ty, [T[_]] => (s: Sym[T]) =>
        s.lam(bound(0, a, hints))(w => s.lam(bound(1, b, hints))(x => s.lam(bound(2, c, hints))(y =>
          s.lam(bound(3, d, hints))(z => f(Term.bound(s, w), Term.bound(s, x), Term.bound(s, y), Term.bound(s, z))
            .run(s)))))))

  given five[A, B, C, D, E, R](using a: RocqType[A], b: RocqType[B], c: RocqType[C], d: RocqType[D], e: RocqType[E],
      r: RocqType[R]): DefineShape[(A, B, C, D, E) => R] with
    type Lam = (Term[A], Term[B], Term[C], Term[D], Term[E]) => Term[R]
    val types: List[RocqType[?]] = List(a, b, c, d, e)
    def rocqType: RocqType[(A, B, C, D, E) => R] = RocqType[(A, B, C, D, E) => R]
    def body(f: Lam, hints: List[String]): (List[Binder], Term[?]) =
      val xs = types.zipWithIndex.map((t, i) => binder(i, t, hints))
      (xs, f(Term.free(xs(0)), Term.free(xs(1)), Term.free(xs(2)), Term.free(xs(3)), Term.free(xs(4))))
    def made(name: DefName, f: Lam, hints: List[String], lambda: Deferred[Written[Lambda]])
        : Definition[(A, B, C, D, E) => R] =
      spot(name, lambda, Body(name, RocqType[A => B => C => D => E => R].ty, [T[_]] => (s: Sym[T]) =>
        s.lam(bound(0, a, hints))(v => s.lam(bound(1, b, hints))(w => s.lam(bound(2, c, hints))(x =>
          s.lam(bound(3, d, hints))(y => s.lam(bound(4, e, hints))(z =>
            f(Term.bound(s, v), Term.bound(s, w), Term.bound(s, x), Term.bound(s, y), Term.bound(s, z)).run(s))))))))

  given six[A, B, C, D, E, G, R](using a: RocqType[A], b: RocqType[B], c: RocqType[C], d: RocqType[D],
      e: RocqType[E], g: RocqType[G], r: RocqType[R]): DefineShape[(A, B, C, D, E, G) => R] with
    type Lam = (Term[A], Term[B], Term[C], Term[D], Term[E], Term[G]) => Term[R]
    val types: List[RocqType[?]] = List(a, b, c, d, e, g)
    def rocqType: RocqType[(A, B, C, D, E, G) => R] = RocqType[(A, B, C, D, E, G) => R]
    def body(f: Lam, hints: List[String]): (List[Binder], Term[?]) =
      val xs = types.zipWithIndex.map((t, i) => binder(i, t, hints))
      (xs, f(Term.free(xs(0)), Term.free(xs(1)), Term.free(xs(2)), Term.free(xs(3)), Term.free(xs(4)),
        Term.free(xs(5))))
    def made(name: DefName, f: Lam, hints: List[String], lambda: Deferred[Written[Lambda]])
        : Definition[(A, B, C, D, E, G) => R] =
      spot(name, lambda, Body(name, RocqType[A => B => C => D => E => G => R].ty, [T[_]] => (s: Sym[T]) =>
        s.lam(bound(0, a, hints))(u => s.lam(bound(1, b, hints))(v => s.lam(bound(2, c, hints))(w =>
          s.lam(bound(3, d, hints))(x => s.lam(bound(4, e, hints))(y => s.lam(bound(5, g, hints))(z =>
            f(Term.bound(s, u), Term.bound(s, v), Term.bound(s, w), Term.bound(s, x), Term.bound(s, y),
              Term.bound(s, z)).run(s)))))))))

  /** A lambda's `i`th input as the IR binds it: level `i`, named as the developer named it. */
  def binder(i: Int, t: RocqType[?], hints: List[String]): Binder = Binder(VarId.level(i), hint(i, hints), t.ty)

  private def spot[F: RocqType](name: DefName, lambda: Deferred[Written[Lambda]], b: Body[?]): Definition[F] =
    Definition.onTheSpot(OnTheSpot(name, Code.Proven(name), lambda, Spot.Define(b)))

  private def bound[A](i: Int, t: RocqType[A], hints: List[String]): Bound[A] = Bound(hint(i, hints), t.ty)
  private def hint(i: Int, hints: List[String]): String = hints.lift(i).getOrElse("x")
