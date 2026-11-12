package frflow.dsl.shape

import frflow.core.name.DefName
import frflow.dsl.build.WrittenAt
import frflow.dsl.term.{LeanType, Term}
import frflow.dsl.vocab.{Definition, Stating}
import scala.collection.concurrent.TrieMap

/** `stated { (a: Term[A], …) => body }`: a define whose body may apply a Declaration, so it is used only where a
  * statement is written (`Stating`), as a Declaration is: plain code and a define not itself `stated` do not compile
  * calling it, and it is no Definition code could be given. Its body is read in the statement's `Stating`. It is a
  * define like any other in the vocabulary and to the prover.
  */
final class Stated[F] private[shape] (val name: DefName, build: Stating => Definition[F]):
  // One define per reading of the statements (whether they are closed), so every
  // statement of one elaboration names the same define, which the vocabulary keeps once (`Declarations`).
  private val built = TrieMap.empty[Boolean, Definition[F]]

  /** The define as the statements being written read it. */
  private[shape] def in(st: Stating): Definition[F] = built.getOrElseUpdate(st.closing, build(st))

object Stated:
  /** The define named `name` written `at`, its body read in each `Stating` it is applied in by `build`. */
  def of[F](name: DefName, at: WrittenAt)(build: DefName => Stating => Definition[F]): Stated[F] =
    new Stated(name, st => build(name)(st).in(at))

  /** A `stated` define's lambda `L`, of inputs' and result's terms: the Definition's type it makes, and its shape. */
  trait Shaped[L]:
    type F
    def shape: DefineShape[F] { type Lam = L }

  object Shaped:
    given one[A: LeanType, R: LeanType]: Shaped[Term[A] => Term[R]] with
      type F = A => R
      def shape: DefineShape.one[A, R] = DefineShape.one[A, R]
    given two[A: LeanType, B: LeanType, R: LeanType]: Shaped[(Term[A], Term[B]) => Term[R]] with
      type F = (A, B) => R
      def shape: DefineShape.two[A, B, R] = DefineShape.two[A, B, R]
    given three[A: LeanType, B: LeanType, C: LeanType, R: LeanType]: Shaped[(Term[A], Term[B], Term[C]) => Term[R]]
    with
      type F = (A, B, C) => R
      def shape: DefineShape.three[A, B, C, R] = DefineShape.three[A, B, C, R]
    given four[A: LeanType, B: LeanType, C: LeanType, D: LeanType, R: LeanType]
        : Shaped[(Term[A], Term[B], Term[C], Term[D]) => Term[R]] with
      type F = (A, B, C, D) => R
      def shape: DefineShape.four[A, B, C, D, R] = DefineShape.four[A, B, C, D, R]
    given five[A: LeanType, B: LeanType, C: LeanType, D: LeanType, E: LeanType, R: LeanType]
        : Shaped[(Term[A], Term[B], Term[C], Term[D], Term[E]) => Term[R]] with
      type F = (A, B, C, D, E) => R
      def shape: DefineShape.five[A, B, C, D, E, R] = DefineShape.five[A, B, C, D, E, R]
    given six[A: LeanType, B: LeanType, C: LeanType, D: LeanType, E: LeanType, G: LeanType, R: LeanType]
        : Shaped[(Term[A], Term[B], Term[C], Term[D], Term[E], Term[G]) => Term[R]] with
      type F = (A, B, C, D, E, G) => R
      def shape: DefineShape.six[A, B, C, D, E, G, R] = DefineShape.six[A, B, C, D, E, G, R]

  extension [A, R](d: Stated[A => R])
    def apply(a: Term[A])(using st: Stating, r: LeanType[R]): Term[R] = d.in(st)(a)
  extension [A, B, R](d: Stated[(A, B) => R])
    def apply(a: Term[A], b: Term[B])(using st: Stating, ta: LeanType[A], tb: LeanType[B], r: LeanType[R]): Term[R] =
      d.in(st)(a, b)
  extension [A, B, C, R](d: Stated[(A, B, C) => R])
    def apply(a: Term[A], b: Term[B], c: Term[C])(using st: Stating, ta: LeanType[A], tb: LeanType[B],
        tc: LeanType[C], r: LeanType[R]): Term[R] = d.in(st)(a, b, c)
  extension [A, B, C, D, R](d: Stated[(A, B, C, D) => R])
    def apply(a: Term[A], b: Term[B], c: Term[C], e: Term[D])(using st: Stating, ta: LeanType[A], tb: LeanType[B],
        tc: LeanType[C], td: LeanType[D], r: LeanType[R]): Term[R] = d.in(st)(a, b, c, e)
  extension [A, B, C, D, E, R](d: Stated[(A, B, C, D, E) => R])
    def apply(a: Term[A], b: Term[B], c: Term[C], e: Term[D], f: Term[E])(using st: Stating, ta: LeanType[A],
        tb: LeanType[B], tc: LeanType[C], td: LeanType[D], te: LeanType[E], r: LeanType[R]): Term[R] =
      d.in(st)(a, b, c, e, f)
  extension [A, B, C, D, E, G, R](d: Stated[(A, B, C, D, E, G) => R])
    def apply(a: Term[A], b: Term[B], c: Term[C], e: Term[D], f: Term[E], g: Term[G])(using st: Stating,
        ta: LeanType[A], tb: LeanType[B], tc: LeanType[C], td: LeanType[D], te: LeanType[E], tg: LeanType[G],
        r: LeanType[R]): Term[R] = d.in(st)(a, b, c, e, f, g)
