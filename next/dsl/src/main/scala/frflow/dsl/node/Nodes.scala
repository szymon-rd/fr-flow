package frflow.dsl.node

import cats.data.NonEmptyList
import cats.syntax.all.*
import frflow.core.name.RelPath
import frflow.core.spec.{Reliance, Statement}
import frflow.dsl.build.{AsWritten, Deferred, Fault, Site}
import frflow.dsl.shape.Elab
import frflow.dsl.model.Fact
import frflow.dsl.term.Term

/** The plain methods the DSL's inline constructors call once they have the source text and position. */
object Nodes:
  def claim(head: Head, formula: () => Term[Boolean], written: AsWritten): Node =
    Node(head, Elab.formula(Site.Node(head.id), formula, written).map(Statement.Claim(_, Reliance.Relied)))

  /** A fact about the outside is said whole (`Fact`): its term is the assumption's formula. */
  def assumption(head: Head, formula: () => Term[Boolean] | Fact, written: AsWritten): Node =
    val term = () => formula() match
      case f: Fact          => f.term
      case t: Term[Boolean] => t
    Node(head, Elab.formula(Site.Node(head.id), term, written).map(Statement.Assumption(_)))

  def design(head: Head, governs: NonEmptyList[String]): Node =
    Node(head, governs.traverse(path(head, _)).map(Statement.Design(_)))

  private def path(head: Head, p: String): Deferred[RelPath] =
    RelPath.parse(p).fold(why => Deferred.failed(Site.Node(head.id), Fault.BadPath(p, why)), Deferred.pure)
