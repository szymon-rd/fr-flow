package frflow.dsl.lifted

import frflow.core.name.DefName
import frflow.dsl.build.{AsWritten, Site, WrittenAt}
import frflow.dsl.shape.{DefineShape, Elab}
import frflow.dsl.term.{LeanType, Term}
import frflow.dsl.vocab.Definition

/** The Definition lifted code is, made as `define` makes one: named as its val, its lambda the term read from the
  * Scala (over its inputs' terms), its text the Scala as written. One maker per number of inputs.
  */
object Lifting:
  def one[A: FrSpec, R: FrSpec](name: DefName, at: WrittenAt, written: AsWritten)(body: Term[A] => Term[R])
      : Definition[A => R] = made(name, at, written)(DefineShape.one[A, R])(body)

  def two[A: FrSpec, B: FrSpec, R: FrSpec](name: DefName, at: WrittenAt, written: AsWritten)(
      body: (Term[A], Term[B]) => Term[R]): Definition[(A, B) => R] =
    made(name, at, written)(DefineShape.two[A, B, R])(body)

  def three[A: FrSpec, B: FrSpec, C: FrSpec, R: FrSpec](name: DefName, at: WrittenAt, written: AsWritten)(
      body: (Term[A], Term[B], Term[C]) => Term[R]): Definition[(A, B, C) => R] =
    made(name, at, written)(DefineShape.three[A, B, C, R])(body)

  def four[A: FrSpec, B: FrSpec, C: FrSpec, D: FrSpec, R: FrSpec](name: DefName, at: WrittenAt, written: AsWritten)(
      body: (Term[A], Term[B], Term[C], Term[D]) => Term[R]): Definition[(A, B, C, D) => R] =
    made(name, at, written)(DefineShape.four[A, B, C, D, R])(body)

  /** A contract written with the DSL (`FrSpec.whereStated`): a define of the value's term. */
  def stated[A: LeanType](name: DefName, at: WrittenAt, written: AsWritten)(rule: Term[A] => Term[Boolean])
      : Definition[A => Boolean] = made(name, at, written)(DefineShape.one[A, Boolean])(rule)

  private def made[F](name: DefName, at: WrittenAt, written: AsWritten)(shape: DefineShape[F])(body: shape.Lam)
      : Definition[F] =
    shape.made(name, body, written.params,
      Elab.lambda(Site.Define(name), shape.types)(() => shape.body(body, written.params), written)).in(at)
