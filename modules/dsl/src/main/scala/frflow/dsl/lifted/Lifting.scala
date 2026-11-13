package frflow.dsl.lifted

import frflow.core.name.DefName
import frflow.dsl.build.{AsWritten, Site, WrittenAt}
import frflow.dsl.shape.{DefineShape, Elab}
import frflow.dsl.term.{LeanType, Term}
import frflow.dsl.vocab.Definition

/** The Definition code FrFlow reads is (a class's member), made as `define` makes one: named, its lambda the term
  * read from the Scala (over its inputs' terms), its text the Scala as written. One maker per number of inputs.
  */
object Lifting:
  def one[A: FrSpec, R: FrSpec](name: DefName, at: WrittenAt, written: AsWritten)(body: Term[A] => Term[R])
      : Definition[A => R] = made(DefineShape.one[A, R])(name, written)(body).in(at)

  def two[A: FrSpec, B: FrSpec, R: FrSpec](name: DefName, at: WrittenAt, written: AsWritten)(
      body: (Term[A], Term[B]) => Term[R]): Definition[(A, B) => R] =
    made(DefineShape.two[A, B, R])(name, written)(body).in(at)

  def three[A: FrSpec, B: FrSpec, C: FrSpec, R: FrSpec](name: DefName, at: WrittenAt, written: AsWritten)(
      body: (Term[A], Term[B], Term[C]) => Term[R]): Definition[(A, B, C) => R] =
    made(DefineShape.three[A, B, C, R])(name, written)(body).in(at)

  def four[A: FrSpec, B: FrSpec, C: FrSpec, D: FrSpec, R: FrSpec](name: DefName, at: WrittenAt, written: AsWritten)(
      body: (Term[A], Term[B], Term[C], Term[D]) => Term[R]): Definition[(A, B, C, D) => R] =
    made(DefineShape.four[A, B, C, D, R])(name, written)(body).in(at)

  /** A type's contract (`FrSpec.where`): a define of the value's term. */
  def stated[A: LeanType](name: DefName, at: WrittenAt, written: AsWritten)(rule: Term[A] => Term[Boolean])
      : Definition[A => Boolean] = made(DefineShape.one[A, Boolean])(name, written)(rule).in(at)

  private def made[F](shape: DefineShape[F])(name: DefName, written: AsWritten)(body: shape.Lam): Definition[F] =
    shape.made(name, body, written.params,
      Elab.lambda(Site.Define(name), shape.types)(() => shape.body(body, written.params), written))
