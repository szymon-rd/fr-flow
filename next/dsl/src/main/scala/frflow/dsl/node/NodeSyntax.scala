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

    /** The claim fixes a word the nodes above leave open: they do not rely on it for that word. */
    def leftOpenAbove: Node = n.copy(statement = n.statement.andThen {
      case c @ Statement.Claim(_, _) => Deferred.pure(c.copy(reliance = Reliance.LeftOpen))
      case _                         => Deferred.failed(Site.Node(n.head.id), Fault.NotAClaim("leftOpenAbove"))
    })

  private def linked(n: Node)(f: Links => Links): Node = n.copy(head = n.head.copy(links = f(n.head.links)))
