package frflow.proof.obligation

import cats.Order
import frflow.core.name.NodeId

/** What Lean is asked: the name of its theorem (`lean.lower.LowerObligation.name` spells it). Of a node: `complete`,
  * `impl`, `cover_<op>`, `made_<maker>`, its tries. Of the theory as a whole: `consistent_<i>`, `start_<node>`,
  * `inhabited_<node>`, `satisfiable_<i>_<node>`, and each example's `example_<i>`.
  */
enum ObligationName:
  case Complete, Feasible, Impl, RootImpl
  case Cover(op: String)
  case Made(maker: String)
  case Tried(kind: TryKind)
  case Commute(i: Int)
  case Consistent(group: Int)
  case Start(node: NodeId)
  case Inhabited(node: NodeId)
  case Satisfiable(node: NodeId, i: Int)
  case Example(i: Int)

object ObligationName:
  given Order[ObligationName] = Order.by(_.toString)
