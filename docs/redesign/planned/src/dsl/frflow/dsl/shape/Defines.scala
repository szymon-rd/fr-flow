package frflow.dsl.shape

import frflow.core.code.Code
import frflow.core.name.DefName
import frflow.core.term.Program
import frflow.dsl.build.{Site, Source}
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

  inline def program[A: LeanType, R: LeanType](inline body: Term[A] => Recorded[Term[R]]): Definition[A => Program[R]] =
    named(DefName(Source.valName))(name => Definition.onTheSpot[A => Program[R]](OnTheSpot(name, Code.ProvenFlow(name),
      Elab.program(Site.Define(name), LeanType[A], LeanType[R])(body, Source.of(body)), None)))
  // … for 0 to 6 inputs.

  /** A define of shape `b`, named as its val (`name`, read before any val of this method is bound: the name is the
    * developer's val's); its lambda's text and parameter names read where it is written.
    */
  private inline def made[F](inline name: DefName, b: DefineShape[F])(inline body: b.Lam): Definition[F] =
    named(name)(n => b.made(n, body, Source.of(body).params,
      Elab.lambda(Site.Define(n), b.types)(() => b.body(body, Source.of(body).params), Source.of(body))))

  private def named[A](name: DefName)(f: DefName => A): A = f(name)
