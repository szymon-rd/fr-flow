package frflow.proof.obligation

import cats.Order
import frflow.core.name.NodeId

/** What the prover is asked: the name of its theorem (`prover.lower.LowerObligation.name` spells it). Of a node:
  * `complete`, `impl`, `made_<maker>`, `outside`, its tries. Of the theory as a whole: `consistent_<i>`,
  * `inhabited_<node>`, `satisfiable_<i>_<node>`, and each example's `example_<set>_<i>` (the `i`th of
  * its set, whatever order the sets are read in) with its opposite, `example_<set>_<i>_opposite` (the claims give
  * its negation: they contradict it).
  */
enum ObligationName:
  case Complete, Feasible, Impl, RootImpl, Outside
  case Made(maker: String)
  case Tried(kind: TryKind)
  case Consistent(group: Int)
  case Inhabited(node: NodeId)
  case Satisfiable(node: NodeId, i: Int)
  case Example(of: String, i: Int)
  case ExampleOpposite(of: String, i: Int)

object ObligationName:
  given Order[ObligationName] = Order.by(_.toString)
