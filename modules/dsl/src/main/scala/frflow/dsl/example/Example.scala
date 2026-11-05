package frflow.dsl.example

import cats.syntax.all.*
import frflow.core.example.{Example as Elaborated, Given}
import frflow.core.expr.Expr
import frflow.core.spec.Written
import frflow.dsl.build.{Deferred, Site}

/** One example as a test writes it (owner §18): its name, the values it gives provided Definitions, and its fact,
  * built when elaborated.
  */
final case class Example(name: String, bindings: List[Binding], fact: Deferred[Written[Expr]]):
  def elaborated: Deferred[Elaborated] =
    (bindings.traverse(bound), fact).mapN(Elaborated(name, _, _))

  private def bound(b: Binding): Deferred[Given] =
    b.value.fold(Deferred.failed(Site.Example(name), _), v => Deferred.pure(Given(b.of, v)))
