package frflow.dsl.node

import cats.syntax.all.*
import frflow.core.spec.Statement
import frflow.dsl.build.Deferred
import scala.util.NotGiven

/** The fluent methods of nodes, each on the kinds it applies to. */
object NodeSyntax:
  extension [S <: Statement, F](n: Node[S, F])(using NotGiven[S <:< Statement.Definition])
    def under(wholes: (Node[?, ?] | Null)*): Node[S, F] =
      linked(n)(l => l.copy(under = l.under ++ wholes.map(Parent.of)))
    def replaces(other: Node[?, ?] | Null): Node[S, F] = linked(n)(_.copy(replaces = Some(Parent.of(other))))
    def exempt(invariant: Node[Statement.Invariant, ?] | Null, because: String): Node[S, F] =
      linked(n)(l => l.copy(keeping = l.keeping :+ Keeping.Exempt(Parent.of(invariant), because)))

  extension [S <: Statement, F](c: Node[S, F])(using k: OnPromise[S])
    def examples(givens: Binding*)(cases: Case[F]*): Node[S, F] =
      c.copy(statement = (c.statement, k.examples(c.head, givens.toList, cases.toList)).mapN(k.withExamples))

  extension [S <: Statement, F](c: Node[S, F])(using k: OnContract[S])
    def leftOpenAbove: Node[S, F] = c.copy(statement = c.statement.map(k.leftOpen))

  private def linked[S <: Statement, F](n: Node[S, F])(f: Links => Links): Node[S, F] =
    n.copy(head = n.head.copy(links = f(n.head.links)))
