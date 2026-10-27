package frflow.dsl.shape

import frflow.core.code.Code
import frflow.core.name.DefName
import frflow.core.term.Program
import frflow.core.expr.Binder
import frflow.dsl.build.{AsWritten, Site, Source}
import frflow.dsl.flow.Recorded
import frflow.dsl.term.{LeanType, Term}
import frflow.dsl.vocab.{Definition, OnTheSpot}

/** `define { (a: Term[A], …) => body }`: a Definition given its meaning on the spot (owner §15), named as its val,
  * called by name in terms, its IR built when elaborated; and `program { (a: Term[A]) => Expiry(database.recording)
  * .run(a) }`: a Definition whose meaning is a program over boundaries, recorded once on its input's variable and read
  * into a define whose body is its steps (`Expr.Do`), the meaning `implementProven` gives the Definition the claims
  * speak of.
  */
object Defines:
  inline def define[A: LeanType, R: LeanType](inline body: Term[A] => Term[R]): Definition[A => R] =
    made(DefName(Source.valName), DefineShape.one[A, R])(body)
  inline def define[A: LeanType, B: LeanType, R: LeanType](inline body: (Term[A], Term[B]) => Term[R])
      : Definition[(A, B) => R] =
    made(DefName(Source.valName), DefineShape.two[A, B, R])(body)

  inline def define[A: LeanType, B: LeanType, C: LeanType, R: LeanType](
      inline body: (Term[A], Term[B], Term[C]) => Term[R]): Definition[(A, B, C) => R] =
    made(DefName(Source.valName), DefineShape.three[A, B, C, R])(body)
  inline def define[A: LeanType, B: LeanType, C: LeanType, D: LeanType, R: LeanType](
      inline body: (Term[A], Term[B], Term[C], Term[D]) => Term[R]): Definition[(A, B, C, D) => R] =
    made(DefName(Source.valName), DefineShape.four[A, B, C, D, R])(body)

  inline def define[A: LeanType, B: LeanType, C: LeanType, D: LeanType, E: LeanType, R: LeanType](
      inline body: (Term[A], Term[B], Term[C], Term[D], Term[E]) => Term[R]): Definition[(A, B, C, D, E) => R] =
    made(DefName(Source.valName), DefineShape.five[A, B, C, D, E, R])(body)
  inline def define[A: LeanType, B: LeanType, C: LeanType, D: LeanType, E: LeanType, G: LeanType, R: LeanType](
      inline body: (Term[A], Term[B], Term[C], Term[D], Term[E], Term[G]) => Term[R])
      : Definition[(A, B, C, D, E, G) => R] =
    made(DefName(Source.valName), DefineShape.six[A, B, C, D, E, G, R])(body)

  /** A program of no input: its steps recorded once. */
  inline def program[R: LeanType](inline body: Recorded[Term[R]]): Definition[Program[R]] =
    recorded[Program[R], R](DefName(Source.valName), Nil, Source.of(body))(_ => body)
  inline def program[A: LeanType, R: LeanType](inline body: Term[A] => Recorded[Term[R]]): Definition[A => Program[R]] =
    recorded[A => Program[R], R](DefName(Source.valName), List(LeanType[A]), Source.of(body)) { xs =>
      body(Term.free(xs(0))) }
  inline def program[A: LeanType, B: LeanType, R: LeanType](inline body: (Term[A], Term[B]) => Recorded[Term[R]])
      : Definition[(A, B) => Program[R]] =
    recorded[(A, B) => Program[R], R](DefName(Source.valName), List(LeanType[A], LeanType[B]), Source.of(body)) { xs =>
      body(Term.free(xs(0)), Term.free(xs(1))) }
  inline def program[A: LeanType, B: LeanType, C: LeanType, R: LeanType](
      inline body: (Term[A], Term[B], Term[C]) => Recorded[Term[R]]): Definition[(A, B, C) => Program[R]] =
    recorded[(A, B, C) => Program[R], R](DefName(Source.valName), List(LeanType[A], LeanType[B], LeanType[C]),
      Source.of(body))(xs => body(Term.free(xs(0)), Term.free(xs(1)), Term.free(xs(2))))

  /** A program's Definition: its steps recorded on its inputs' variables (`xs`, one per input, in order). */
  private def recorded[F: LeanType, R: LeanType](name: DefName, inputs: List[LeanType[?]], written: AsWritten)(
      steps: Vector[Binder] => Recorded[Term[R]]): Definition[F] =
    Definition.onTheSpot[F](OnTheSpot(name, Code.ProvenFlow(name),
      Elab.program(Site.Define(name), inputs, LeanType[R])(steps, written), None))

  /** A define of shape `b`, named as its val (`name`, read before any val of this method is bound: the name is the
    * developer's val's); its lambda's text and parameter names read where it is written.
    */
  private inline def made[F](inline name: DefName, b: DefineShape[F])(inline body: b.Lam): Definition[F] =
    named(name)(n => b.made(n, body, Source.of(body).params,
      Elab.lambda(Site.Define(n), b.types)(() => b.body(body, Source.of(body).params), Source.of(body))))

  private def named[A](name: DefName)(f: DefName => A): A = f(name)
