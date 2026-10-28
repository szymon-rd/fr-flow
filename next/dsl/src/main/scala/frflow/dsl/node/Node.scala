package frflow.dsl.node

import cats.data.NonEmptyList
import frflow.core.spec.Statement
import frflow.dsl.build.{Deferred, Source}
import frflow.dsl.term.Term
import frflow.dsl.vocab.Stating

/** A node as the model writes it, its id its val's name as written (`val grantWhenFree = Node.claim(…)` is
  * `grantWhenFree`). Three kinds and no other (owner §15): a claim and an assumption are a sentence and a formula,
  * the one proven (or tested), the other trusted; a design is a decision about code no proof covers. How a claim is
  * checked is read off its formula and what defines the Definitions it mentions, never written beside it.
  */
final case class Node(head: Head, statement: Deferred[Statement])

object Node:
  /** A claim: `forall` over every possible value; `always[T](x => …)`, every value of `T` that can be made;
    * `always(stored)(s => …)`, every state the store reaches. It constrains every Declaration and Definition it
    * mentions.
    */
  inline def claim(statement: String)(inline formula: Stating ?=> Term[Boolean]): Node =
    Nodes.claim(Head.make(Source.valName, statement, Source.file, Source.offset), () => formula(using Stating.writing),
      Source.of(Node.writing(formula)))

  /** The same form, trusted: the world outside (`store.behavesAs(stored)`: the store does what its model does, and
    * nothing outside the code changes it; `stored.initially(held => held === Nil)`; `store.atomic`), what values from
    * outside always meet (`always[Booking](b => …)`), or an outside system's promise.
    */
  inline def assumption(statement: String)(inline formula: Stating ?=> Term[Boolean]): Node =
    Nodes.assumption(Head.make(Source.valName, statement, Source.file, Source.offset),
      () => formula(using Stating.writing), Source.of(Node.writing(formula)))

  /** A statement's formula, written where a statement is being written. */
  inline def writing(inline formula: Stating ?=> Term[Boolean]): Term[Boolean] = formula(using Stating.writing)

  inline def design(statement: String)(governs: String, more: String*): Node =
    Nodes.design(Head.make(Source.valName, statement, Source.file, Source.offset), NonEmptyList(governs, more.toList))
