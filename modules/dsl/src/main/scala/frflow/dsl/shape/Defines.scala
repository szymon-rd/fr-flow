package frflow.dsl.shape

import frflow.core.name.DefName
import frflow.dsl.build.{AsWritten, Site, Source, WrittenAt}
import frflow.dsl.term.{LeanType, Term}
import frflow.dsl.vocab.{Definition, Stating}
import scala.compiletime.summonInline

/** `define { (a: Term[A], …) => body }`: a Definition given its meaning on the spot (owner §15), named as its val,
  * called by name in terms, its IR built when elaborated. It records the file it is written in (`Definition.in`).
  */
object Defines:
  inline def define[A: LeanType, R: LeanType](inline body: Term[A] => Term[R]): Definition[A => R] =
    made(DefName(Source.valName), DefineShape.one[A, R])(body).in(WrittenAt.in(Source.here))
  inline def define[A: LeanType, B: LeanType, R: LeanType](inline body: (Term[A], Term[B]) => Term[R])
      : Definition[(A, B) => R] =
    made(DefName(Source.valName), DefineShape.two[A, B, R])(body).in(WrittenAt.in(Source.here))

  inline def define[A: LeanType, B: LeanType, C: LeanType, R: LeanType](
      inline body: (Term[A], Term[B], Term[C]) => Term[R]): Definition[(A, B, C) => R] =
    made(DefName(Source.valName), DefineShape.three[A, B, C, R])(body).in(WrittenAt.in(Source.here))
  inline def define[A: LeanType, B: LeanType, C: LeanType, D: LeanType, R: LeanType](
      inline body: (Term[A], Term[B], Term[C], Term[D]) => Term[R]): Definition[(A, B, C, D) => R] =
    made(DefName(Source.valName), DefineShape.four[A, B, C, D, R])(body).in(WrittenAt.in(Source.here))

  inline def define[A: LeanType, B: LeanType, C: LeanType, D: LeanType, E: LeanType, R: LeanType](
      inline body: (Term[A], Term[B], Term[C], Term[D], Term[E]) => Term[R]): Definition[(A, B, C, D, E) => R] =
    made(DefName(Source.valName), DefineShape.five[A, B, C, D, E, R])(body).in(WrittenAt.in(Source.here))
  inline def define[A: LeanType, B: LeanType, C: LeanType, D: LeanType, E: LeanType, G: LeanType, R: LeanType](
      inline body: (Term[A], Term[B], Term[C], Term[D], Term[E], Term[G]) => Term[R])
      : Definition[(A, B, C, D, E, G) => R] =
    made(DefName(Source.valName), DefineShape.six[A, B, C, D, E, G, R])(body).in(WrittenAt.in(Source.here))

  /** A define of the type `F`, its lambda's shape found by that type: what a Declaration is given
    * (`granted.define { (held, request) => … }`).
    */
  inline def of[F](inline body: Lam[F]): Definition[F] =
    named(DefName(Source.valName))(shaped(_, summonInline[DefineShape[F]], Source.of(body))(body))
      .in(WrittenAt.in(Source.here))

  /** A define's lambda over its inputs' terms, by the define's type. */
  type Lam[F] = F match
    case Function1[a, r]                => Term[a] => Term[r]
    case Function2[a, b, r]             => (Term[a], Term[b]) => Term[r]
    case Function3[a, b, c, r]          => (Term[a], Term[b], Term[c]) => Term[r]
    case Function4[a, b, c, d, r]       => (Term[a], Term[b], Term[c], Term[d]) => Term[r]
    case Function5[a, b, c, d, e, r]    => (Term[a], Term[b], Term[c], Term[d], Term[e]) => Term[r]
    case Function6[a, b, c, d, e, g, r] => (Term[a], Term[b], Term[c], Term[d], Term[e], Term[g]) => Term[r]

  /** The define of shape `b` whose lambda is `body`: `Lam[F]` is `b.Lam`, each read off the one type `F`. */
  def shaped[F](n: DefName, b: DefineShape[F], written: AsWritten)(body: Any): Definition[F] =
    madeOf(n, b, written)(body.asInstanceOf[b.Lam])

  /** `stated { (a: Term[A], …) => body }`: a define whose body may apply a Declaration, used only in statements
    * (`Stated`), to six inputs. One method for every arity, the lambda's shape found by its type (`Stated.Shaped`):
    * overloads would type the lambda before giving it the `Stating` its body reads.
    */
  inline def stated[L](inline body: Stating ?=> L)(using l: Stated.Shaped[L]): Stated[l.F] =
    Stated.of(DefName(Source.valName), WrittenAt.in(Source.here))(n =>
      st => madeOf(n, l.shape, Source.of(body(using Stating.probing)))(body(using st)))

  /** A define of shape `b`, named as its val (`name`, read before any val of this method is bound: the name is the
    * developer's val's); its lambda's text and parameter names read where it is written.
    */
  private inline def made[F](inline name: DefName, b: DefineShape[F])(inline body: b.Lam): Definition[F] =
    named(name)(madeOf(_, b, Source.of(body))(body))

  /** A define of shape `b` named `n`, its lambda written as `written` says. */
  private def madeOf[F](n: DefName, b: DefineShape[F], written: AsWritten)(body: b.Lam): Definition[F] =
    b.made(n, body, written.params, Elab.lambda(Site.Define(n), b.types)(() => b.body(body, written.params), written))

  private def named[A](name: DefName)(f: DefName => A): A = f(name)
