package frflow.dsl.node

import cats.data.NonEmptyList
import frflow.core.spec.{Prose, Statement}
import frflow.dsl.build.{Deferred, Site, Source}
import frflow.dsl.shape.{CallShape, Elab}
import frflow.dsl.term.{Param, Term}

/** A node as the model writes it. `S` is the statement's case, so fluent methods exist only where they apply. */
final case class Node[S <: Statement, F](head: Head, statement: Deferred[S])

object Node:
  inline def claim(id: String, statement: String, why: String)(
      inline formula: Term[Boolean]): Node[Statement.Claim, Unit] =
    Nodes.claim(Heads.make(id, Prose(statement, why), Source.file, Source.offset), () => formula, Source.of(formula))

  inline def contract[F](op: Param[F])(using s: CallShape[F])(id: String, statement: String, why: String)(
      inline post: s.Lam[Term[Boolean]]): Node[s.Made, F] =
    val head = Heads.make(id, Prose(statement, why), Source.file, Source.offset)
    Node(head, s.contract(op, Elab.lambda(Site.Node(head.id), s.types)(s.call(post, _), Source.of(post))))

  inline def design(id: String, statement: String, why: String)(governs: String, more: String*)
      : Node[Statement.Design, Unit] =
    Nodes.design(Heads.make(id, Prose(statement, why), Source.file, Source.offset), NonEmptyList(governs, more.toList))
  // … `invariant`, `assumption` (a fact, an operation's promise, a boundary's model) and `definition`, the same way.
