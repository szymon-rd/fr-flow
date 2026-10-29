package frflow.dsl.node

import cats.data.NonEmptyList
import cats.syntax.all.*
import frflow.core.name.RelPath
import frflow.core.spec.{Reliance, Statement}
import frflow.core.term.Sym
import frflow.dsl.build.{AsWritten, Deferred, Fault, Site}
import frflow.dsl.shape.Elab
import frflow.dsl.model.Fact
import frflow.dsl.term.{Notes, Term}
import frflow.dsl.vocab.Stating

/** The plain methods the DSL's inline constructors call once they have the source text and position. */
object Nodes:
  def claim(head: Head, formula: Stating => () => Term[Boolean], written: AsWritten): Node =
    Node(head, st => Elab.formula(Site.Node(head.id), () => closed(st, formula(st)()), written)
      .map(Statement.Claim(_, Reliance.Relied)))

  /** A fact about the outside is said whole (`Fact`): its term is the assumption's formula. */
  def assumption(head: Head, formula: Stating => () => Term[Boolean] | Fact, written: AsWritten): Node =
    def term(st: Stating) = () => formula(st)() match
      case f: Fact          => f.term
      case t: Term[Boolean] => closed(st, t)
    Node(head, st => Elab.formula(Site.Node(head.id), term(st), written).map(Statement.Assumption(_)))

  def design(head: Head, governs: NonEmptyList[String]): Node =
    val statement = governs.traverse(path(head, _)).map(Statement.Design(_))
    Node(head, _ => statement)

  /** The formula over the world it holds in (`Closing`), once what changes with the World is known. */
  private def closed(st: Stating, t: Term[Boolean]): Term[Boolean] =
    if st.closing then Closing.of(t).fold(refused, identity) else t

  /** A statement refused where it is closed: its fault alone (read open, its leading variables are another's). */
  private def refused(f: Fault): Term[Boolean] =
    Term.noted(Notes.fault(f))([T[_]] => (s: Sym[T]) => s.bool(true))

  private def path(head: Head, p: String): Deferred[RelPath] =
    RelPath.parse(p).fold(why => Deferred.failed(Site.Node(head.id), Fault.BadPath(p, why)), Deferred.pure)
