package frflow.dsl.node

import cats.data.NonEmptyList
import cats.syntax.all.*
import frflow.core.name.RelPath
import frflow.core.spec.{Reliance, Statement}
import frflow.core.term.language.Sym
import frflow.dsl.build.{AsWritten, Deferred, Fault, Site}
import frflow.dsl.shape.Elab
import frflow.dsl.term.{Notes, Term}
import frflow.dsl.vocab.Stating

/** The plain methods the DSL's inline constructors call once they have the source text and position. */
object Nodes:
  def claim(head: Head, formula: Stating => () => Term[Boolean], written: AsWritten): Node =
    Node(head, st => Elab.formula(Site.Node(head.id), () => closed(st, Standing.closing(st, formula)), written)
      .map(Statement.Claim(_, Reliance.Relied)))

  /** An assumption over a structure is said of it in every state, as a claim is (`Standing`): what is assumed of
    * one no class is read for (`ledger.provided`).
    */
  def assumption(head: Head, formula: Stating => () => Term[Boolean], written: AsWritten): Node =
    Node(head, st => Elab.formula(Site.Node(head.id), () => closed(st, Standing.closing(st, formula)), written)
      .map(Statement.Assumption(_)))

  def design(head: Head, governs: NonEmptyList[String]): Node =
    val statement = governs.traverse(path(head, _)).map(Statement.Design(_))
    Node(head, _ => statement)

  /** The formula as its node holds it (`Closing`); read open while what it reads is being learnt. */
  private def closed(st: Stating, t: Term[Boolean]): Term[Boolean] =
    if st.closing then Closing.of(t).fold(refused, identity) else Closing.opened(t)

  /** A statement refused where it is closed: its fault alone (read open, its leading variables are another's). */
  private def refused(f: Fault): Term[Boolean] =
    Term.noted(Notes.fault(f))([T[_]] => (s: Sym[T]) => s.bool(true))

  private def path(head: Head, p: String): Deferred[RelPath] =
    RelPath.parse(p).fold(why => Deferred.failed(Site.Node(head.id), Fault.BadPath(p, why)), Deferred.pure)
