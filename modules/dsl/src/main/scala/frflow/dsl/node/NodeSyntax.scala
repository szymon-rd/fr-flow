package frflow.dsl.node

import frflow.core.spec.{Reliance, Statement}
import frflow.dsl.build.{Deferred, Fault, Site}

/** The fluent methods of nodes: the edges (`.refines`, `.assuming`, `.replaces`) and how the nodes above stand to a
  * claim (`.leftOpenAbove`).
  */
object NodeSyntax:
  extension (n: Node)
    /** The node refines `wholes` (the refinement calculus' word): what it says, with its siblings', gives theirs. */
    def refines(wholes: (Node | Null)*): Node = linked(n)(l => l.copy(refines = l.refines ++ wholes.map(Parent.of)))
    /** Its proof takes `premises` as hypotheses: assumptions only (a rule it uses is found, never listed). */
    def assuming(premises: (Node | Null)*): Node =
      linked(n)(l => l.copy(assumes = l.assumes ++ premises.map(Parent.of)))
    def replaces(other: Node | Null): Node = linked(n)(_.copy(replaces = Some(Parent.of(other))))
    /** The claim is from `parts`: each is a part of it, as if it said `.refines` of the claim. What a claim is
      * proven from is then read where the claim is stated. A part may be declared after the claim.
      */
    inline def from(inline parts: (Node | Null)*): Node = NodeSyntax.fromLater(n, () => parts)
    /** What an assumption is about, in the model's own words (the JDK, who uses the code, what happens in time):
      * its kind. Nothing is proven or checked by it; a model lists its assumptions by it.
      */
    def about(kind: String): Node = n.copy(head = n.head.copy(about = Some(kind)))

    /** The claim fixes a word the nodes above leave open: they do not rely on it for that word. */
    def leftOpenAbove: Node = n.copy(statement = st => n.statement(st).andThen {
      case c @ Statement.Claim(_, _) => Deferred.pure(c.copy(reliance = Reliance.LeftOpen))
      case _                         => Deferred.failed(Site.Node(n.head.id), Fault.NotAClaim("leftOpenAbove"))
    })

  /** What `.from` writes: the parts are read when the node's edges are (`Edges`). */
  def fromLater(n: Node, parts: () => Seq[Node | Null]): Node = linked(n)(l => l.copy(parts = l.parts :+ parts))

  private def linked(n: Node)(f: Links => Links): Node = n.copy(head = n.head.copy(links = f(n.head.links)))
